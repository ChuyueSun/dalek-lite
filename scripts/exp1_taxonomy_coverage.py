#!/usr/bin/env python3
"""
Experiment 1: Gap Taxonomy Coverage Audit

Walks all .rs files under src/lemmas/, parses every `pub proof fn` and
`pub broadcast proof fn`, extracts the ensures clause, and classifies it
into a taxonomy of gap types.

Output: /root/experiment_results/exp1_taxonomy_coverage.json
"""

import json
import os
import re
import sys
from collections import defaultdict
from pathlib import Path

LEMMAS_ROOT = Path("/root/dalek-lite/curve25519-dalek/src/lemmas")
OUTPUT_PATH = Path("/root/experiment_results/exp1_taxonomy_coverage.json")

# ---------------------------------------------------------------------------
# 1. Parsing helpers
# ---------------------------------------------------------------------------

def read_file(path: Path) -> str:
    with open(path, "r", encoding="utf-8", errors="replace") as f:
        return f.read()


def extract_proof_fns(source: str, filepath: str):
    """
    Yield dicts for every `pub proof fn` / `pub broadcast proof fn` found
    in *source*.  Each dict contains:
      name, filepath, requires, ensures
    """
    # We need to handle the Verus syntax carefully.
    # Pattern: `pub proof fn NAME(...)` or `pub broadcast proof fn NAME(...)`
    # followed optionally by `requires ... ensures ...` and then `{`
    #
    # Strategy: find the fn header, then scan forward to find requires/ensures
    # blocks up to the body-opening `{`.

    # Match function declarations (handles multi-line)
    fn_pattern = re.compile(
        r'pub\s+(?:broadcast\s+)?proof\s+fn\s+(\w+)\s*(?:<[^>]*>)?\s*\(',
        re.DOTALL
    )

    results = []
    for m in fn_pattern.finditer(source):
        fn_name = m.group(1)
        start_pos = m.start()

        # Find the end of the parameter list (matching parens)
        paren_start = source.index('(', m.start() + len(m.group(0)) - 1)
        paren_depth = 0
        pos = paren_start
        while pos < len(source):
            ch = source[pos]
            if ch == '(':
                paren_depth += 1
            elif ch == ')':
                paren_depth -= 1
                if paren_depth == 0:
                    break
            pos += 1
        after_params = pos + 1

        # Now scan forward for requires/ensures/{ (the body opening brace)
        # We need to find the body-opening brace, handling nested braces in
        # attributes, etc.
        #
        # The structure after params is:
        #   [by (tactic)]? [requires ...]? [ensures ...]? {
        #
        # We scan for `requires`, `ensures`, and the body `{`.

        # Find the opening brace of the body.
        # We need to be careful: `by (bit_vector)` or `by (compute)` might appear.
        # The body brace is the first `{` that is NOT inside `by (...)`.

        # Collect the text between after_params and the body opening brace.
        # We look for the pattern: everything up to a `{` that starts the body.

        # Simple approach: find `requires` and `ensures` keywords that appear
        # as standalone tokens before the body.

        # First, let's find the body opening brace by tracking brace depth.
        # But we must skip braces inside `by (...)` clauses within requires/ensures.
        # Actually in Verus, the body `{` is at depth 0 after the fn signature.

        # Let's find the next `{` that is at the function-signature level.
        # We'll scan character by character, but skip parenthesized sections.

        scan_pos = after_params
        body_brace_pos = None

        # Simple heuristic: scan for `{` while tracking paren depth
        # (to skip `by (...)` blocks)
        p_depth = 0
        while scan_pos < len(source):
            ch = source[scan_pos]
            if ch == '(':
                p_depth += 1
            elif ch == ')':
                p_depth -= 1
            elif ch == '{' and p_depth == 0:
                body_brace_pos = scan_pos
                break
            scan_pos += 1

        if body_brace_pos is None:
            continue

        # Extract the signature region (between params close and body open)
        sig_region = source[after_params:body_brace_pos]

        # Parse out requires and ensures blocks from sig_region
        requires_text = ""
        ensures_text = ""

        # Find positions of `requires` and `ensures` keywords
        req_match = re.search(r'\brequires\b', sig_region)
        ens_match = re.search(r'\bensures\b', sig_region)

        if req_match and ens_match:
            requires_text = sig_region[req_match.end():ens_match.start()].strip()
            ensures_text = sig_region[ens_match.end():].strip()
        elif req_match and not ens_match:
            requires_text = sig_region[req_match.end():].strip()
        elif ens_match and not req_match:
            ensures_text = sig_region[ens_match.end():].strip()

        # Determine if it's a broadcast proof fn
        header_text = source[start_pos:m.end()]
        is_broadcast = 'broadcast' in header_text

        results.append({
            "name": fn_name,
            "filepath": filepath,
            "is_broadcast": is_broadcast,
            "requires": requires_text,
            "ensures": ensures_text,
        })

    return results


# ---------------------------------------------------------------------------
# 2. Expand macros
# ---------------------------------------------------------------------------

def expand_macro_generated_fns(source: str, filepath: str):
    """
    Handle common macro patterns that generate pub proof fn or
    pub broadcast proof fn.  Returns a list of dicts similar to
    extract_proof_fns.
    """
    results = []

    # Pattern 1: macro invocations like:
    #   lemma_bitwise_or_zero_is_id!(lemma_u8_bitwise_or_zero_is_id, u8);
    # where the macro was defined earlier with `pub broadcast proof fn $name`
    #
    # We look for macro_rules! definitions that contain `pub proof fn` or
    # `pub broadcast proof fn`, then find all invocations.

    # Find macro definitions
    macro_defs = {}
    macro_pattern = re.compile(
        r'macro_rules!\s+(\w+)\s*\{(.*?)\n\s*\}',
        re.DOTALL
    )
    for m in macro_pattern.finditer(source):
        macro_name = m.group(1)
        macro_body = m.group(2)

        # Check if this macro generates proof fns
        if 'proof fn' in macro_body:
            # Extract the ensures clause template
            ens_match = re.search(r'\bensures\b(.*?)(?:\{)', macro_body, re.DOTALL)
            ensures_template = ""
            if ens_match:
                ensures_template = ens_match.group(1).strip()

            is_broadcast = 'broadcast proof fn' in macro_body
            macro_defs[macro_name] = {
                "ensures_template": ensures_template,
                "is_broadcast": is_broadcast,
            }

    # Find macro invocations
    invocation_pattern = re.compile(r'(\w+)!\s*\(\s*(\w+)')
    for m in invocation_pattern.finditer(source):
        macro_name = m.group(1)
        fn_name = m.group(2)

        if macro_name in macro_defs:
            info = macro_defs[macro_name]
            results.append({
                "name": fn_name,
                "filepath": filepath,
                "is_broadcast": info["is_broadcast"],
                "requires": "",
                "ensures": info["ensures_template"],
                "macro_generated": True,
            })

    return results


# ---------------------------------------------------------------------------
# 3. Classification
# ---------------------------------------------------------------------------

TAXONOMY_ORDER = [
    "serialization_roundtrip",
    "representation_equivalence",
    "bounds_propagation",
    "bounds_weakening",
    "modular_arithmetic",
    "algebraic_rewrite",
    "extensional_equality",
    "concrete_computation",
    "overflow_safety",
    "structural_validity",
    "power_chain",
    "algorithm_step",
    "conditional_sign",
]


def classify(entry: dict) -> str:
    """Classify a proof fn entry into exactly one taxonomy category."""
    ens = entry["ensures"]
    req = entry.get("requires", "")
    name = entry["name"]
    combined = ens + " " + req  # sometimes context from requires helps

    # Normalise whitespace for matching
    ens_n = " ".join(ens.split())
    name_lower = name.lower()
    combined_n = " ".join(combined.split())

    # --- serialization_roundtrip ---
    if "roundtrip" in ens_n.lower() or "roundtrip" in name_lower:
        return "serialization_roundtrip"
    if "as_bytes" in ens_n and "from_bytes" in ens_n:
        return "serialization_roundtrip"
    if "as_bytes" in name_lower and "from_bytes" in name_lower:
        return "serialization_roundtrip"
    # Also catch byte-conversion roundtrip patterns
    if ("to_bytes" in name_lower and "from_bytes" in name_lower):
        return "serialization_roundtrip"
    # Byte serialization helpers (canonical_check, seq_from32, as_bytes, etc.)
    if re.search(r'as_bytes|to_bytes|from_bytes|bytes_to|limbs_to_bytes', name_lower):
        return "serialization_roundtrip"
    if re.search(r'canonical_bytes|canonical_check|seq_from32|u8_32_from_nat|seq_eq.*array', name_lower):
        return "serialization_roundtrip"
    if re.search(r'seq_from32|u8_32_from_nat|fe51_as_bytes|spec_fe51_as_bytes', ens_n):
        return "serialization_roundtrip"

    # --- representation_equivalence ---
    # Pattern: ensures clause has `as_nat` or `as_canonical_nat` with `==`
    # connecting two representation forms
    if re.search(r'as_nat|as_canonical_nat|u64_5_as_nat', ens_n):
        # Check it's an equivalence (== connecting representations)
        if '==' in ens_n:
            # But not if it's purely bounds
            if not re.search(r'<\s*\(?\s*1u\d+\s*<<', ens_n):
                # Check it's not purely a modular arithmetic identity
                if '% p()' not in ens_n and '% group_order()' not in ens_n:
                    return "representation_equivalence"
                # If it has `% p()` but also has representation functions, it's still rep equiv
                if re.search(r'fe51_as_canonical_nat|u64_5_as_nat|spec_add_fe51_limbs|spec_mul', ens_n):
                    return "representation_equivalence"
    # Also: point representation conversions
    if re.search(r'_as_affine|affine_niels_point_as_|projective_niels_point_as_|edwards_point_as_affine', ens_n):
        if '==' in ens_n:
            return "representation_equivalence"
    # Load/conversion lemma: one spec function equals another
    if re.search(r'load\d+_at|_version.*==.*_version|_is_spec', name_lower):
        return "representation_equivalence"
    # spec_mul_internal commutativity, spec equivalences
    if re.search(r'spec_mul_internal|spec_\w+\s*\(.*==.*spec_\w+', ens_n):
        return "representation_equivalence"

    # --- bounds_propagation ---
    if re.search(r'fe51_limbs_bounded|limbs_bounded', ens_n):
        # Check if it's weakening (requires has a tighter bound)
        if re.search(r'fe51_limbs_bounded|limbs_bounded', req):
            # Could be bounds_weakening if the ensures bound is strictly larger
            req_bounds = re.findall(r'(?:fe51_limbs_bounded|limbs_bounded)\s*\([^,]+,\s*(\d+)', req)
            ens_bounds = re.findall(r'(?:fe51_limbs_bounded|limbs_bounded)\s*\([^,]+,\s*(\d+)', ens_n)
            if req_bounds and ens_bounds:
                try:
                    req_max = max(int(b) for b in req_bounds)
                    ens_max = max(int(b) for b in ens_bounds)
                    if ens_max > req_max:
                        return "bounds_weakening"
                except ValueError:
                    pass
        return "bounds_propagation"
    if re.search(r'\bbounded\b', ens_n) and not re.search(r'on_curve|is_valid|valid_', ens_n):
        return "bounds_propagation"
    if re.search(r'<\s*\(?\s*1u\d+\s*<<', ens_n) and '==' not in ens_n:
        return "bounds_propagation"
    # Limb-level bounds like `limbs[i] < X`
    if re.search(r'limbs\[\d+\]\s*<', ens_n) and '==' not in ens_n:
        return "bounds_propagation"
    # Ensures with `< p()` as main conclusion
    if re.search(r'<\s*p\(\)', ens_n) and '==' not in ens_n:
        return "bounds_propagation"
    # Byte bounds like `bytes[31] <= 127`
    if re.search(r'bytes\[\d+\]\s*<=', ens_n):
        return "bounds_propagation"

    # --- modular_arithmetic ---
    if re.search(r'%\s*p\(\)', ens_n) or re.search(r'%\s*group_order\(\)', ens_n):
        return "modular_arithmetic"
    if re.search(r'%\s*\(p\(\)', ens_n):
        return "modular_arithmetic"
    # Modular arithmetic with generic modulus: `% L`, `% m`, `% d`, `% modulus`
    if re.search(r'%\s*(L|m|d|modulus|prime)\b', ens_n):
        return "modular_arithmetic"
    # Division/mod lemmas: `(a + b) / k`, `% d == 0`, etc.
    if re.search(r'%\s*\w+\s*==\s*0', ens_n):
        return "modular_arithmetic"
    if re.search(r'/\s*\w+\s*==|%\s*\w+\s*==', ens_n) and re.search(r'div|mod', name_lower):
        return "modular_arithmetic"
    # field_mul / field_add / field_sub / field_square results
    if re.search(r'field_(mul|add|sub|square|inv|neg)\s*\(', ens_n):
        # Could be algebraic_rewrite or modular_arithmetic
        # If it rewrites one field expression to another, it's algebraic
        if re.search(r'field_(mul|add|sub|square|inv|neg)\s*\(.*==.*field_(mul|add|sub|square|inv|neg)', ens_n):
            return "algebraic_rewrite"
        # If it equates a field op result to 0 or 1
        if re.search(r'field_(mul|add|sub|square|inv|neg)\s*\([^)]*\)\s*==\s*[01]\b', ens_n):
            return "algebraic_rewrite"
        return "modular_arithmetic"

    # --- algebraic_rewrite ---
    if re.search(r'field_(add|mul|inv|neg|sub|square)', ens_n):
        return "algebraic_rewrite"
    # Edwards curve group operations: edwards_add, edwards_double, edwards_neg, etc.
    if re.search(r'edwards_(add|double|neg|scalar_mul|identity)', ens_n):
        return "algebraic_rewrite"
    # Montgomery curve group operations
    if re.search(r'montgomery_(add|neg|scalar_mul)', ens_n):
        return "algebraic_rewrite"
    # field_sqrt / field_abs / canonical_sqrt
    if re.search(r'field_sqrt|field_abs|canonical_sqrt', ens_n):
        return "algebraic_rewrite"
    # Pure integer algebraic identities: distributive, commutative, associative
    if re.search(r'distributiv|commutativ|associativ', name_lower):
        return "algebraic_rewrite"
    # Integer algebra lemmas with * and + rearrangement
    if re.search(r'\*.*\+.*==.*\*|\+.*\*.*==.*\+', ens_n) and not re.search(r'%|pow|<<|>>', ens_n):
        return "algebraic_rewrite"
    # Product square factorize, quad product, reorder lemmas
    if re.search(r'product_square|quad_prod|reorder|factorize', name_lower):
        return "algebraic_rewrite"
    # Multiplication lemmas that rearrange products
    if re.search(r'lemma_mul_\w*(distributive|commutative|si_vi|w0)', name_lower):
        return "algebraic_rewrite"
    # is_sqrt_ratio / sqrt_ratio lemmas
    if re.search(r'is_sqrt_ratio|sqrt_ratio|invsqrt|nonneg_square_root', ens_n) or \
       re.search(r'sqrt_ratio|invsqrt|nonneg_square', name_lower):
        return "algebraic_rewrite"

    # --- extensional_equality ---
    if re.search(r'=~=|forall.*==.*limbs|a\s*==\s*b', ens_n):
        if 'forall' in ens_n and 'limbs' in ens_n:
            return "extensional_equality"
        if '=~=' in ens_n:
            return "extensional_equality"
        # a == b from limbs
        if re.search(r'\w+\s*==\s*\w+', ens_n) and 'limbs' in combined_n:
            return "extensional_equality"
    # Array/seq equality: forall|i| ... bytes1[i] == bytes2[i]
    if re.search(r'forall.*bytes\d*\[', ens_n):
        return "extensional_equality"
    # *bytes1 == *bytes2 (dereferenced equality)
    if re.search(r'\*\w+\s*==\s*\*\w+', ens_n):
        return "extensional_equality"
    # x == y simple equality from structural arguments (unique results)
    if re.search(r'unique|implies_x_zero|implies_zero|r == s|r == t|x1 == x2|x == 0\b', ens_n):
        return "extensional_equality"
    if re.search(r'unique', name_lower):
        return "extensional_equality"

    # --- concrete_computation ---
    concrete_constants = [
        'EDWARDS_D', 'SQRT_M1', 'ONE', 'ZERO', 'one_field_element',
        'zero_field_element', 'MONTGOMERY_A', 'EDWARDS_D2',
        'EDWARDS_D_MINUS_ONE_SQUARED', 'ONE_MINUS_EDWARDS_D_SQUARED',
        'SQRT_AD_MINUS_ONE', 'INVSQRT_A_MINUS_D', 'MONTGOMERY_A_NEG',
    ]
    for const in concrete_constants:
        if const in ens_n:
            # Make sure it's talking about the value of the constant
            return "concrete_computation"
    # Specific numeric constant references
    if re.search(r'486660|spec_ed25519_basepoint|spec_x25519_basepoint', ens_n):
        return "concrete_computation"
    if 'basepoint' in name_lower:
        return "concrete_computation"

    # --- overflow_safety ---
    if re.search(r'u64::MAX|u128::MAX|no.?overflow|< u\d+::MAX', ens_n):
        return "overflow_safety"
    if re.search(r'<=\s*u64::MAX|<=\s*u128::MAX', ens_n):
        return "overflow_safety"
    if re.search(r'\d+u\d+\s*<<\s*\d+.*==', ens_n) and not re.search(r'field_|pow|as_nat', ens_n):
        # Bit-shift arithmetic identity not involving field ops
        return "overflow_safety"
    # Cast-is-mod lemmas (u128 as u8 == x % 256)
    if re.search(r'cast.*mod|as \$uN.*%', ens_n) or re.search(r'cast_u\d+_is_mod', name_lower):
        return "overflow_safety"
    # Bitwise operations: or, and, shift
    if re.search(r'\|.*==|&.*==|>>.*==|<<.*==', ens_n) and not re.search(r'field_|edwards_|montgomery_', ens_n):
        return "overflow_safety"

    # --- structural_validity ---
    if re.search(r'on_curve|is_on_edwards|valid_extended|valid_projective|is_valid|curve_eq|satisfies_curve', ens_n):
        return "structural_validity"
    if re.search(r'on_curve|is_on_edwards|valid_extended|valid_projective|is_valid', name_lower):
        return "structural_validity"
    # is_in_even_subgroup, subgroup properties
    if re.search(r'is_in_even_subgroup|even_subgroup|is_square|not_square|quadratic_residue', ens_n):
        return "structural_validity"
    if re.search(r'is_square|quadratic_residue', name_lower):
        return "structural_validity"

    # --- power_chain ---
    if re.search(r'pow\(|pow2\(|pow2k|exponent', ens_n):
        return "power_chain"
    if 'pow_chain' in name_lower or 'pow22501' in name_lower or 'pow_p58' in name_lower:
        return "power_chain"
    if 'pow2k' in name_lower:
        return "power_chain"

    # --- algorithm_step ---
    algo_keywords = [
        'step', 'invariant', 'induction', 'loop', 'iteration',
        'pippenger', 'straus', 'partial', 'accumul', 'reconstruct',
        'radix', 'naf', 'sum_up_to', 'scalar_mul', 'double_base',
        'mul_base', 'select_is', 'vartime', 'digit',
        'column_sum', 'running_sum', 'bucket', 'batch_compress',
        'elligator', 'decompress', 'batch_invert',
    ]
    for kw in algo_keywords:
        if kw in name_lower:
            return "algorithm_step"
    if re.search(r'sum_up_to|partial_sum|loop_inv|reconstruct|running_sum|column_sum|bucket', ens_n):
        return "algorithm_step"
    # Ristretto compress/decompress
    if re.search(r'ristretto_compress|ristretto_decode', ens_n):
        return "algorithm_step"

    # --- conditional_sign ---
    if re.search(r'conditional_negate|conditional_select|sign.?bit|negate', name_lower):
        return "conditional_sign"
    if re.search(r'conditional_negate|conditional_select|sign_bit', ens_n):
        return "conditional_sign"

    # --- Additional heuristics for remaining items ---

    # Number theory lemmas: gcd, prime, binomial, bezout, euclid
    if re.search(r'gcd|prime|binomial|bezout|euclid|coprime|divides|divisib', name_lower):
        return "modular_arithmetic"
    if re.search(r'spec_gcd|spec_extended_gcd|binomial', ens_n):
        return "modular_arithmetic"
    # p() % 2, group_order() % 2, odd/even properties of primes
    if re.search(r'p\(\)\s*%|group_order\(\)\s*%', ens_n):
        return "modular_arithmetic"
    # Generic modular: `% \d+ ==` or `% m ==`
    if re.search(r'%\s*\d+\s*==|%\s*\w+\s*==', ens_n):
        return "modular_arithmetic"
    # negation_sums_to_zero, product_of_complements
    if re.search(r'negation|complement', name_lower):
        return "modular_arithmetic"
    # Congruence lemmas
    if re.search(r'congruence|congruent', name_lower):
        return "modular_arithmetic"

    # Bit manipulation lemmas (bitwise or, and, shift, mask)
    if re.search(r'bit_or|bit_and|shr|shl|shift|mask|>>|<<', ens_n):
        return "overflow_safety"
    if re.search(r'bit_or|bit_and|shr|shl|shift|mask|bitwise', name_lower):
        return "overflow_safety"

    # Modular arithmetic by name
    if re.search(r'mod_|div_mod|mul_mod|add_mod', name_lower):
        return "modular_arithmetic"

    # Bounds by name
    if re.search(r'bound|overflow|no_underflow', name_lower):
        return "bounds_propagation"

    # Montgomery reduce
    if re.search(r'montgomery_reduce|mont_reduce', name_lower):
        return "modular_arithmetic"

    # Reduce lemmas
    if 'reduce' in name_lower and 'spec_reduce' in ens_n:
        return "bounds_propagation"

    # Integer multiplication/division lemmas with <= or < conclusion
    if re.search(r'lemma_mul_(lt|le)\b', name_lower):
        return "bounds_propagation"
    if re.search(r'mul_le_implies|div_le|div_of_sum', name_lower):
        return "bounds_propagation"
    # lemma_m (multiplication bound)
    if name_lower == 'lemma_m':
        return "bounds_propagation"

    # Bits-as-nat lemmas
    if re.search(r'bits_as_nat|byte_bits|bits_from_index', name_lower):
        return "representation_equivalence"

    # Equality from ==
    if re.search(r'\w+\s*==\s*\w+', ens_n) and len(ens_n) < 80:
        # Short equality ensures -- likely extensional or concrete
        if re.search(r'spec_', ens_n):
            return "representation_equivalence"

    # Montgomery curve specific lemmas about identity, lift, etc.
    if re.search(r'montgomery_lift|montgomery_add.*Infinity|montgomery_add.*identity', ens_n):
        return "algebraic_rewrite"

    # Catch remaining implies/propagation patterns
    if re.search(r'==>', ens_n):
        # Implication with modular content
        if '%' in ens_n:
            return "modular_arithmetic"
        # Implication about structural properties
        if re.search(r'is_|on_|valid_', ens_n):
            return "structural_validity"

    # Boolean not results (!is_square etc.)
    if re.search(r'!is_square|!is_', ens_n):
        return "structural_validity"

    # Misc: v != 0 (nonzero results)
    if re.search(r'!= 0\b|v != 0|x != 0', ens_n):
        return "modular_arithmetic"

    # Catch-all: if ensures has `% p` or `% \w+` with bounds, it's modular
    if re.search(r'%\s*\w+', ens_n) and re.search(r'<=|<|>=|>', ens_n):
        return "modular_arithmetic"

    # Simple equality conclusion `u == 0` or `x == 0` from algebraic argument
    if re.search(r'\w+\s*==\s*0\b', ens_n):
        return "algebraic_rewrite"

    return "UNKNOWN"


# ---------------------------------------------------------------------------
# 4. Layer classification
# ---------------------------------------------------------------------------

def get_layer(filepath: str) -> str:
    """Return the subdirectory layer name for a file."""
    rel = os.path.relpath(filepath, str(LEMMAS_ROOT))
    parts = Path(rel).parts
    if len(parts) > 1:
        return parts[0]
    else:
        # Top-level file like scalar_lemmas.rs
        stem = Path(rel).stem
        # Group related top-level files
        if 'scalar' in stem:
            return 'scalar_lemmas'
        elif 'montgomery' in stem:
            return 'montgomery_lemmas'
        elif 'ristretto' in stem:
            return 'ristretto_lemmas'
        return stem


# ---------------------------------------------------------------------------
# 5. Main
# ---------------------------------------------------------------------------

def main():
    all_entries = []

    # Walk all .rs files
    for root, dirs, files in os.walk(LEMMAS_ROOT):
        for fname in sorted(files):
            if not fname.endswith('.rs'):
                continue
            fpath = os.path.join(root, fname)
            source = read_file(Path(fpath))

            # Extract directly-written proof fns
            fns = extract_proof_fns(source, fpath)
            all_entries.extend(fns)

            # Extract macro-generated proof fns
            macro_fns = expand_macro_generated_fns(source, fpath)
            # Deduplicate: only add macro fns whose names aren't already found
            existing_names = {e["name"] for e in fns}
            for mf in macro_fns:
                if mf["name"] not in existing_names:
                    all_entries.append(mf)

    # Classify each entry
    for entry in all_entries:
        entry["category"] = classify(entry)

    # --------------- Build summary ---------------
    total = len(all_entries)

    # Per-category stats
    cat_entries = defaultdict(list)
    for e in all_entries:
        cat_entries[e["category"]].append(e["name"])

    classified = {}
    for cat in TAXONOMY_ORDER + ["UNKNOWN"]:
        names = cat_entries.get(cat, [])
        count = len(names)
        pct = round(100.0 * count / total, 1) if total else 0
        classified[cat] = {
            "count": count,
            "pct": pct,
            "examples": names[:5],
        }

    unknown_count = len(cat_entries.get("UNKNOWN", []))
    coverage_rate = round((total - unknown_count) / total, 4) if total else 0

    # Per-layer stats
    layer_entries = defaultdict(list)
    for e in all_entries:
        layer = get_layer(e["filepath"])
        layer_entries[layer].append(e)

    per_layer = {}
    for layer, entries in sorted(layer_entries.items()):
        layer_total = len(entries)
        layer_classified = sum(1 for e in entries if e["category"] != "UNKNOWN")
        # Top types in this layer
        layer_cats = defaultdict(int)
        for e in entries:
            layer_cats[e["category"]] += 1
        top_types = sorted(layer_cats.items(), key=lambda x: -x[1])[:5]
        per_layer[layer] = {
            "total": layer_total,
            "classified": layer_classified,
            "top_types": [{"type": t, "count": c} for t, c in top_types],
        }

    result = {
        "total_proof_fns": total,
        "classified": classified,
        "coverage_rate": coverage_rate,
        "per_layer": per_layer,
    }

    # Also include the detailed list for downstream use
    detail = []
    for e in all_entries:
        detail.append({
            "name": e["name"],
            "filepath": os.path.relpath(e["filepath"], str(LEMMAS_ROOT)),
            "category": e["category"],
            "is_broadcast": e.get("is_broadcast", False),
            "ensures_snippet": e["ensures"][:200],
        })
    result["detail"] = detail

    # Write output
    OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    with open(OUTPUT_PATH, "w") as f:
        json.dump(result, f, indent=2)

    # Print summary to stdout
    print(f"Total proof fns found: {total}")
    print(f"Coverage rate: {coverage_rate:.1%}")
    print()
    print(f"{'Category':<30} {'Count':>6} {'Pct':>7}")
    print("-" * 45)
    for cat in TAXONOMY_ORDER + ["UNKNOWN"]:
        info = classified[cat]
        print(f"{cat:<30} {info['count']:>6} {info['pct']:>6.1f}%")
    print()
    print("Per-layer breakdown:")
    for layer, info in sorted(per_layer.items()):
        print(f"  {layer}: {info['total']} total, {info['classified']} classified")
        for t in info["top_types"]:
            print(f"    - {t['type']}: {t['count']}")

    print(f"\nOutput saved to {OUTPUT_PATH}")


if __name__ == "__main__":
    main()
