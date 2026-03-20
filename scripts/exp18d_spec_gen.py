#!/usr/bin/env python3
"""
Exp 18d: Spec Generation Recipe Testing

Phase A: Single-pass spec generation for 8 functions
Phase B: Bounds supplement for field functions
Phase E: Reactive strengthening for too-weak specs
"""

import json
import os
import re
import sys

DALEK_SRC = "/root/dalek-lite/curve25519-dalek/src"
RESULTS_DIR = "/root/dalek-lite/experiment_results/exp18d"

# Function metadata — siblings are from the explore agent's extraction
FUNCTIONS = {
    "C1_add": {
        "function": "add",
        "file": "backend/serial/u64/field.rs",
        "is_field": True,
        "sibling_specs": [
            "fn from_bytes(bytes: &[u8; 32]) -> (r: FieldElement51)\n    ensures\n        fe51_as_nat(&r) == u8_32_as_nat(bytes) % pow2(255),\n        fe51_limbs_bounded(&r, 51),\n        is_uniform_bytes(bytes) ==> is_uniform_field_element(&r),",
            "fn sub(self, _rhs: &'a FieldElement51) -> (output: FieldElement51)\n    ensures\n        output == spec_sub_limbs(self, _rhs),\n        fe51_as_canonical_nat(&output) == field_sub(fe51_as_canonical_nat(self), fe51_as_canonical_nat(_rhs)),\n        fe51_limbs_bounded(&output, 52),\n        fe51_limbs_bounded(&output, 54),"
        ],
        "body_summary": "Limb-wise addition loop: output.limbs[i] = self.limbs[i] + _rhs.limbs[i] for i in 0..5. Proof block calls lemma_field51_add and lemma_add_bounds_propagate.",
        "gt_ensures": "output == spec_add_fe51_limbs(self, _rhs),\n    fe51_as_nat(&output) == fe51_as_nat(self) + fe51_as_nat(_rhs),\n    fe51_as_canonical_nat(&output) == field_add(fe51_as_canonical_nat(self), fe51_as_canonical_nat(_rhs)),\n    fe51_limbs_bounded(self, 51) && fe51_limbs_bounded(_rhs, 51) ==> fe51_limbs_bounded(&output, 52),\n    fe51_limbs_bounded(self, 52) && fe51_limbs_bounded(_rhs, 52) ==> fe51_limbs_bounded(&output, 53),"
    },
    "C2_negate": {
        "function": "negate",
        "file": "backend/serial/u64/field.rs",
        "is_field": True,
        "sibling_specs": [
            "fn square(&self) -> (r: FieldElement51)\n    requires fe51_limbs_bounded(self, 54),\n    ensures\n        fe51_limbs_bounded(&r, 52),\n        fe51_limbs_bounded(&r, 54),\n        fe51_as_canonical_nat(&r) == field_canonical(pow(u64_5_as_nat(self.limbs) as int, 2) as nat),",
            "fn square2(&self) -> (r: FieldElement51)\n    requires fe51_limbs_bounded(self, 54),\n    ensures\n        fe51_as_canonical_nat(&r) == field_canonical((2 * pow(u64_5_as_nat(self.limbs) as int, 2)) as nat),\n        fe51_limbs_bounded(&r, 53),\n        fe51_limbs_bounded(&r, 54),"
        ],
        "body_summary": "Computes 16*p - self, then calls reduce(). Self is mutated. Uses magic numbers 36028797018963664 (16*(2^51-19)) and 36028797018963952 (16*(2^51-1)).",
        "gt_ensures": "fe51_limbs_bounded(self, 52),\n    u64_5_as_nat(self.limbs) == 16 * p() - u64_5_as_nat(old(self).limbs) - p() * ((36028797018963952u64 - old(self).limbs[4]) as u64 >> 51),\n    field_canonical(u64_5_as_nat(self.limbs) + u64_5_as_nat(old(self).limbs)) == 0,\n    self.limbs == spec_negate(old(self).limbs),"
    },
    "C3_reduce": {
        "function": "reduce",
        "file": "backend/serial/u64/field.rs",
        "is_field": True,
        "sibling_specs": [
            "fn pow2k(&self, mut k: u32) -> (r: FieldElement51)\n    requires k > 0, fe51_limbs_bounded(self, 54),\n    ensures\n        fe51_limbs_bounded(&r, 52),\n        fe51_limbs_bounded(&r, 54),\n        fe51_as_canonical_nat(&r) == field_canonical(pow(fe51_as_nat(self) as int, pow2(k as nat)) as nat),",
            "fn from_bytes(bytes: &[u8; 32]) -> (r: FieldElement51)\n    ensures\n        fe51_as_nat(&r) == u8_32_as_nat(bytes) % pow2(255),\n        fe51_limbs_bounded(&r, 51),\n        is_uniform_bytes(bytes) ==> is_uniform_field_element(&r),"
        ],
        "body_summary": "Weak reduction: parallel carry-outs. Extracts carries c0..c4 = limbs[i] >> 51, masks limbs, propagates carries cyclically (c4*19 to limbs[0]).",
        "gt_ensures": "r.limbs == spec_reduce(limbs),\n    (forall|i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 51)) ==> (r.limbs =~= limbs),\n    fe51_as_nat(&r) == u64_5_as_nat(limbs) - p() * (limbs[4] >> 51),\n    fe51_as_canonical_nat(&r) == u64_5_as_field_canonical(limbs),\n    fe51_as_nat(&r) < 2 * p(),"
    },
    "C4_from_bytes": {
        "function": "from_bytes",
        "file": "backend/serial/u64/field.rs",
        "is_field": True,
        "sibling_specs": [
            "fn as_bytes(self) -> (r: [u8; 32])\n    ensures\n        u8_32_as_nat(&r) == fe51_as_canonical_nat(&self),",
            "fn reduce(mut limbs: [u64; 5]) -> (r: FieldElement51)\n    ensures\n        r.limbs == spec_reduce(limbs),\n        (forall|i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 51)) ==> (r.limbs =~= limbs),\n        fe51_as_nat(&r) == u64_5_as_nat(limbs) - p() * (limbs[4] >> 51),\n        fe51_as_canonical_nat(&r) == u64_5_as_field_canonical(limbs),\n        fe51_as_nat(&r) < 2 * p(),"
        ],
        "body_summary": "Deserializes 32 bytes into 5 limbs via load8_at + masking with 51-bit mask. Proof establishes u8_32_as_nat correspondence and calls axiom_from_bytes_uniform.",
        "gt_ensures": "fe51_as_nat(&r) == u8_32_as_nat(bytes) % pow2(255),\n    fe51_limbs_bounded(&r, 51),\n    is_uniform_bytes(bytes) ==> is_uniform_field_element(&r),"
    },
    "C5_compress": {
        "function": "compress",
        "file": "ristretto.rs",
        "is_field": False,
        "sibling_specs": [
            "fn decompress(&self) -> (result: Option<RistrettoPoint>)\n    ensures\n        result.is_none() <==> spec_ristretto_decompress(self.0).is_none(),\n        result.is_some() ==> edwards_point_as_nat(result.unwrap().0) == spec_ristretto_decompress(self.0).unwrap(),\n        result.is_some() ==> is_well_formed_edwards_point(result.unwrap().0),",
            "fn from_slice(bytes: &[u8]) -> (result: Result<CompressedRistretto, TryFromSliceError>)\n    ensures\n        bytes@.len() == 32 ==> matches!(result, Ok(_)),\n        bytes@.len() != 32 ==> matches!(result, Err(_)),",
        ],
        "body_summary": "Ristretto compression: computes u1=(Z+Y)(Z-Y), u2=X*Y, invsqrt, conditional rotation/negation, then serializes s = den_inv * (Z-Y_final) to bytes.",
        "gt_ensures": "result.0 == spec_ristretto_compress(*self),"
    },
    "C6_mul_base_clamped": {
        "function": "mul_base_clamped",
        "file": "montgomery.rs",
        "is_field": False,
        "sibling_specs": [
            "fn mul_base(scalar: &Scalar) -> (result: Self)\n    requires scalar.bytes[31] <= 127,\n    ensures\n        is_valid_montgomery_point(result),\n        montgomery_point_as_nat(result) == montgomery_scalar_mul_u(spec_x25519_basepoint_u(), scalar_as_nat(scalar)),",
            "fn mul_clamped(self, bytes: [u8; 32]) -> (result: Self)\n    requires is_valid_montgomery_point(self),\n    ensures\n        ({ let P = canonical_montgomery_lift(montgomery_point_as_nat(self));\n           let n = u8_32_as_nat(&spec_clamp_integer(bytes));\n           montgomery_point_as_nat(result) == u_coordinate(montgomery_scalar_mul(P, n)) }),",
        ],
        "body_summary": "Clamps input bytes, creates Scalar, calls mul_base. Simple wrapper.",
        "gt_ensures": "is_valid_montgomery_point(result),\n    montgomery_point_as_nat(result) == montgomery_scalar_mul_u(spec_x25519_basepoint_u(), scalar_as_nat(&Scalar { bytes: spec_clamp_integer(bytes) })),"
    },
    "C7_sub": {
        "function": "sub",
        "file": "backend/serial/u64/field.rs",
        "is_field": True,
        "sibling_specs": [
            "fn add(self, _rhs: &'a FieldElement51) -> (output: FieldElement51)\n    ensures\n        output == spec_add_fe51_limbs(self, _rhs),\n        fe51_as_nat(&output) == fe51_as_nat(self) + fe51_as_nat(_rhs),\n        fe51_as_canonical_nat(&output) == field_add(fe51_as_canonical_nat(self), fe51_as_canonical_nat(_rhs)),\n        fe51_limbs_bounded(self, 51) && fe51_limbs_bounded(_rhs, 51) ==> fe51_limbs_bounded(&output, 52),\n        fe51_limbs_bounded(self, 52) && fe51_limbs_bounded(_rhs, 52) ==> fe51_limbs_bounded(&output, 53),",
            "fn mul(self, _rhs: &'a FieldElement51) -> (output: FieldElement51)\n    ensures\n        fe51_as_canonical_nat(&output) == field_mul(fe51_as_canonical_nat(self), fe51_as_canonical_nat(_rhs)),\n        fe51_limbs_bounded(&output, 52),\n        fe51_limbs_bounded(&output, 54),"
        ],
        "body_summary": "Subtraction via add-16p-then-subtract: augments self.limbs with 16*p constants, subtracts _rhs limb-wise, calls reduce(). Proof chains mod_sum_factor and sub_mod_noop lemmas.",
        "gt_ensures": "output == spec_sub_limbs(self, _rhs),\n    fe51_as_canonical_nat(&output) == field_sub(fe51_as_canonical_nat(self), fe51_as_canonical_nat(_rhs)),\n    fe51_limbs_bounded(&output, 52),\n    fe51_limbs_bounded(&output, 54),"
    },
    "C8_pow2k": {
        "function": "pow2k",
        "file": "backend/serial/u64/field.rs",
        "is_field": True,
        "sibling_specs": [
            "fn square(&self) -> (r: FieldElement51)\n    requires fe51_limbs_bounded(self, 54),\n    ensures\n        fe51_limbs_bounded(&r, 52),\n        fe51_limbs_bounded(&r, 54),\n        fe51_as_canonical_nat(&r) == field_canonical(pow(u64_5_as_nat(self.limbs) as int, 2) as nat),",
            "fn square2(&self) -> (r: FieldElement51)\n    requires fe51_limbs_bounded(self, 54),\n    ensures\n        fe51_as_canonical_nat(&r) == field_canonical((2 * pow(u64_5_as_nat(self.limbs) as int, 2)) as nat),\n        fe51_limbs_bounded(&r, 53),\n        fe51_limbs_bounded(&r, 54),"
        ],
        "body_summary": "Repeated squaring k times. Loop: compute schoolbook square (with 19x reduction), carry-propagate. Result = self^(2^k). Uses same mul pattern as mul().",
        "gt_ensures": "fe51_limbs_bounded(&r, 52),\n    fe51_limbs_bounded(&r, 54),\n    fe51_as_canonical_nat(&r) == field_canonical(pow(fe51_as_nat(self) as int, pow2(k as nat)) as nat),"
    },
}


def build_phase_a_prompt(func_id):
    """Phase A: Single-pass spec generation."""
    f = FUNCTIONS[func_id]
    sibling_text = "\n\n".join(f["sibling_specs"])

    return f"""Write the ensures clause for this Verus function.

== FUNCTION ==
Function: {f['function']}
File: {f['file']}

Body summary (the actual exec code and proof blocks):
{f['body_summary']}

== AVAILABLE SPEC FUNCTIONS ==
// From field_specs.rs:
spec fn p() -> nat {{ pow2(255) - 19 }}
spec fn field_add(a: nat, b: nat) -> nat {{ (a + b) % p() }}
spec fn field_sub(a: nat, b: nat) -> nat {{ (a + p() - (b % p())) % p() }}
spec fn field_mul(a: nat, b: nat) -> nat {{ (a * b) % p() }}
spec fn field_neg(x: nat) -> nat {{ (p() - (x % p())) % p() }}
spec fn field_canonical(x: nat) -> nat {{ x % p() }}
spec fn field_square(x: nat) -> nat {{ (x * x) % p() }}

// From field_specs_u64.rs:
spec fn fe51_as_nat(f: &FieldElement51) -> nat {{ u64_5_as_nat(f.limbs) }}
spec fn fe51_as_canonical_nat(f: &FieldElement51) -> nat {{ fe51_as_nat(f) % p() }}
spec fn fe51_limbs_bounded(f: &FieldElement51, n: u32) -> bool {{ forall|i| 0<=i<5 ==> f.limbs[i] < (1u64 << n) }}
spec fn spec_add_fe51_limbs(a: &FE51, b: &FE51) -> FE51 {{ FE51 {{ limbs: [a.limbs[0]+b.limbs[0], ...] }} }}
spec fn spec_sub_limbs(a: &FE51, b: &FE51) -> FE51 {{ ... }}
spec fn spec_negate(limbs: [u64; 5]) -> [u64; 5] {{ ... }}
spec fn spec_reduce(limbs: [u64; 5]) -> [u64; 5] {{ ... }}
spec fn u64_5_as_field_canonical(limbs: [u64; 5]) -> nat {{ u64_5_as_nat(limbs) % p() }}

// Misc:
spec fn is_uniform_bytes(bytes: &[u8; 32]) -> bool
spec fn is_uniform_field_element(f: &FieldElement51) -> bool
spec fn is_valid_montgomery_point(p: MontgomeryPoint) -> bool
spec fn montgomery_scalar_mul_u(u: nat, n: nat) -> nat
spec fn spec_ristretto_compress(p: EdwardsPoint) -> [u8; 32]
spec fn scalar_as_nat(s: &Scalar) -> nat
spec fn spec_clamp_integer(bytes: [u8; 32]) -> [u8; 32]
spec fn spec_x25519_basepoint_u() -> nat

== SIBLING SPECS (for style reference) ==
{sibling_text}

== INSTRUCTION ==
Write the ensures clause for the {f['function']} function. Include:
- The primary algebraic/functional property (what does this compute?)
- Any representation bounds the output satisfies
- Any conditional properties a caller would need to chain operations
- Any statistical/uniformity properties if applicable

Do NOT include properties trivially derivable from other clauses.
Format: one ensures clause per line, indented with 4 spaces.
"""


def build_phase_b_prompt(func_id, phase_a_ensures):
    """Phase B: Bounds supplement."""
    f = FUNCTIONS[func_id]
    sibling_text = "\n\n".join(f["sibling_specs"])

    return f"""Here is a function and its algebraic ensures clause (generated in Phase A):

== FUNCTION ==
{f['function']} in {f['file']}
Body: {f['body_summary']}

== CURRENT ENSURES (from Phase A) ==
ensures
{phase_a_ensures}

== SIBLING BOUNDS PATTERNS ==
{sibling_text}

== INSTRUCTION ==
Does this function need bounds-propagation clauses? Specifically:
- If inputs have limb bounds B, what bounds does the output have?
- Add conditional clauses like:
  fe51_limbs_bounded(input, B) ==> fe51_limbs_bounded(&output, B+K)

Also check:
- Is there a < 2*p() value bound?
- Is there an identity-when-already-reduced property?
- Is there an exact nat-level intermediate formula?

Only add clauses that are NOT trivially derivable from existing ensures.
Output the COMPLETE ensures clause (Phase A clauses + new bounds clauses).
"""


def build_phase_e_prompt(func_id, current_ensures, error_msg):
    """Phase E: Reactive strengthening."""
    f = FUNCTIONS[func_id]

    return f"""A proof of a caller function fails because {f['function']}'s ensures clause
doesn't guarantee a property the caller needs.

== CALLEE ({f['function']}) CURRENT SPEC ==
ensures
{current_ensures}

== ERROR ==
{error_msg}

== INSTRUCTION ==
Propose the minimum additional ensures clause to add to {f['function']} that would
fix the caller's proof. Only add what is necessary — don't add unrelated properties.
Output ONLY the new clause(s) to add.
"""


if __name__ == "__main__":
    os.makedirs(f"{RESULTS_DIR}/prompts", exist_ok=True)
    os.makedirs(f"{RESULTS_DIR}/specs", exist_ok=True)

    if len(sys.argv) < 2:
        print("Usage: python exp18d_spec_gen.py phase_a | phase_b | phase_e | summary")
        sys.exit(1)

    cmd = sys.argv[1]

    if cmd == "phase_a":
        for fid in FUNCTIONS:
            prompt = build_phase_a_prompt(fid)
            path = f"{RESULTS_DIR}/prompts/{fid}_A.txt"
            with open(path, 'w') as f:
                f.write(prompt)
            print(f"  {fid}_A: {len(prompt)} chars")
        print(f"\nTotal: {len(FUNCTIONS)} Phase A prompts")

    elif cmd == "phase_b":
        # Read Phase A results first
        for fid in ["C1_add", "C2_negate", "C3_reduce", "C4_from_bytes", "C7_sub", "C8_pow2k"]:
            spec_file = f"{RESULTS_DIR}/specs/{fid}_A.txt"
            if os.path.exists(spec_file):
                with open(spec_file) as f:
                    phase_a = f.read()
                prompt = build_phase_b_prompt(fid, phase_a)
                path = f"{RESULTS_DIR}/prompts/{fid}_B.txt"
                with open(path, 'w') as f:
                    f.write(prompt)
                print(f"  {fid}_B: {len(prompt)} chars")
            else:
                print(f"  {fid}_B: SKIP (no Phase A result yet)")

    elif cmd == "phase_e":
        # Reactive strengthening for C2 (negate) and C3 (reduce)
        errors = {
            "C2_negate": "error: postcondition not satisfied\n   --> negate_lemmas.rs:42:9\n   |\n42 |     assert(u64_5_as_nat(result.limbs) + u64_5_as_nat(old_limbs) == 15 * p()\n   |            || u64_5_as_nat(result.limbs) + u64_5_as_nat(old_limbs) == 16 * p());\n   |     assertion failed",
            "C3_reduce": "error: postcondition not satisfied\n   --> field.rs:871:13\n   |\n871 |     r.limbs[0] == expected_limbs[0],\n   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ failed this postcondition\n   | note: the caller expected to know the exact limb values after reduce"
        }
        for fid, error in errors.items():
            spec_file = f"{RESULTS_DIR}/specs/{fid}_A.txt"
            if os.path.exists(spec_file):
                with open(spec_file) as f:
                    phase_a = f.read()
                prompt = build_phase_e_prompt(fid, phase_a, error)
                path = f"{RESULTS_DIR}/prompts/{fid}_E.txt"
                with open(path, 'w') as f:
                    f.write(prompt)
                print(f"  {fid}_E: {len(prompt)} chars")

    elif cmd == "summary":
        print("Phase A results:")
        for fid in FUNCTIONS:
            spec_file = f"{RESULTS_DIR}/specs/{fid}_A.txt"
            if os.path.exists(spec_file):
                with open(spec_file) as f:
                    content = f.read()
                # Count ensures clauses
                clauses = [l.strip() for l in content.split('\n') if l.strip() and not l.strip().startswith('//') and not l.strip().startswith('ensures')]
                gt = FUNCTIONS[fid]["gt_ensures"]
                gt_clauses = [l.strip().rstrip(',') for l in gt.split('\n') if l.strip()]
                print(f"  {fid}: {len(clauses)} clauses generated (GT has {len(gt_clauses)})")
            else:
                print(f"  {fid}: no result")
