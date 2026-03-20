#!/usr/bin/env python3
"""Strip all proof function bodies in a Verus file, replacing them with admit().

Key insight: The body `{` is always at paren_depth==0, while ensures `({...})`
is inside parens (paren_depth > 0). Track both to find the real body.
"""

import re
import sys


def find_body_brace(lines, start_line):
    """Find the opening brace of the function body.

    Returns (line_idx, col_idx) of the body opening brace.
    The body brace is the first `{` at paren_depth==0 after the function signature starts.
    We skip the function params `(...)` by tracking paren depth.
    """
    paren_depth = 0
    brace_depth = 0
    past_params = False  # True once we've seen the closing `)` of the function params

    for i in range(start_line, len(lines)):
        for col, ch in enumerate(lines[i]):
            if ch == '(':
                paren_depth += 1
            elif ch == ')':
                paren_depth -= 1
                if paren_depth == 0 and not past_params:
                    past_params = True
            elif ch == '{':
                if paren_depth == 0 and past_params:
                    # This is the body opening brace
                    return (i, col)
                brace_depth += 1
            elif ch == '}':
                if paren_depth == 0:
                    brace_depth -= 1
                # else: closing brace inside parens (e.g., ensures block expr)

    return None


def find_matching_close(lines, open_line, open_col):
    """Find the closing brace matching the one at (open_line, open_col)."""
    depth = 1
    i = open_line
    start_col = open_col + 1

    while i < len(lines):
        start = start_col if i == open_line else 0
        for col in range(start, len(lines[i])):
            ch = lines[i][col]
            if ch == '{':
                depth += 1
            elif ch == '}':
                depth -= 1
                if depth == 0:
                    return (i, col)
        i += 1

    return None


def strip_file(filepath):
    with open(filepath, 'r') as f:
        content = f.read()

    lines = content.split('\n')

    # First pass: find all proof functions and their body ranges
    fn_ranges = []  # (start_line, body_open_line, body_open_col, body_close_line, body_close_col, has_return, return_type)

    i = 0
    while i < len(lines):
        stripped = lines[i].lstrip()
        if re.match(r'(pub\s+)?(broadcast\s+)?proof\s+fn\s+', stripped):
            fn_start = i

            # Check for return type in signature
            # Scan forward to find the body brace
            result = find_body_brace(lines, i)
            if result is None:
                i += 1
                continue

            body_open_line, body_open_col = result

            # Check for return type in the signature (between fn_start and body_open)
            sig_text = '\n'.join(lines[fn_start:body_open_line + 1])
            has_return = '->' in sig_text.split('{')[0] if '{' in sig_text else '->' in sig_text

            return_type = None
            if has_return:
                ret_match = re.search(r'->\s*\(\w+:\s*(\w+)\)', sig_text)
                if ret_match:
                    return_type = ret_match.group(1)

            # Find matching close brace
            close = find_matching_close(lines, body_open_line, body_open_col)
            if close is None:
                i += 1
                continue

            body_close_line, body_close_col = close
            fn_ranges.append((fn_start, body_open_line, body_open_col, body_close_line, body_close_col, has_return, return_type))
            i = body_close_line + 1
        else:
            i += 1

    # Second pass: rebuild the file with stripped bodies
    result = []
    last_line = 0

    for (fn_start, body_open_line, body_open_col, body_close_line, body_close_col, has_return, return_type) in fn_ranges:
        # Copy everything from last_line to body_open_line (the line with opening brace)
        for k in range(last_line, body_open_line):
            result.append(lines[k])

        # Output the opening brace line (up to and including '{')
        result.append(lines[body_open_line][:body_open_col + 1])

        # Output admit() body
        if has_return:
            if return_type == 'int':
                dummy = '0int'
            elif return_type == 'nat':
                dummy = '0nat'
            elif return_type == 'u64':
                dummy = '0u64'
            elif return_type == 'bool':
                dummy = 'false'
            else:
                dummy = 'arbitrary()'
            result.append('    admit();')
            result.append(f'    {dummy}')
        else:
            result.append('    admit();')

        result.append('}')
        last_line = body_close_line + 1

    # Copy remaining lines
    for k in range(last_line, len(lines)):
        result.append(lines[k])

    with open(filepath, 'w') as f:
        f.write('\n'.join(result))

    print(f"Stripped {len(fn_ranges)} functions in {filepath}")


if __name__ == '__main__':
    for fp in sys.argv[1:]:
        strip_file(fp)
