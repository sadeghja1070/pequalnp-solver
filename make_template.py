#!/usr/bin/env python3
"""Turn the accepted proof L_meta_12230.lean (Apache-2.0, open-goat/pequalnp-proofs) into a
template for every 'direction 3' positive step: a monotone six-input f whose AND/OR/NOT circuits
are never smaller than its best AND/OR circuit.  Each replacement must hit exactly the expected
number of places, so a change upstream fails loudly instead of producing a wrong template.
usage: make_template.py <path to L_meta_12230.lean> <out template>"""
import sys

src, out = sys.argv[1], sys.argv[2]
t = open(src, encoding="utf-8").read()


def sub(old, new, count):
    global t
    n = t.count(old)
    if n != count:
        sys.exit("template: expected %d of %r, found %d" % (count, old, n))
    t = t.replace(old, new)


ROWS = """[0xd5b8b62dd5b8b62dfff8fe3ffff8fe3f,
   0x66dd1b4666dd1b463fff1fc73fff1fc7,
   0x78eec3b078eec3b0c07fe3f8c07fe3f8,
   0x8b036cdb8b036cdbff87ffffff87ffff,
   0xbf77fc00bf77fc00007ffc00007ffc00]"""
WITNESS = """⟨[⟨.or, [3, 4]⟩, ⟨.and, [6, 2]⟩, ⟨.and, [7, 1]⟩, ⟨.and, [2, 5]⟩,
    ⟨.or, [9, 6]⟩, ⟨.and, [10, 1]⟩, ⟨.or, [11, 7]⟩, ⟨.and, [12, 0]⟩,
    ⟨.or, [8, 13]⟩], 14⟩"""
STMT_LINE = [l for l in t.split("\n") if l.startswith("theorem PEqualNP.Outside.L_meta_12230 : ")]
if len(STMT_LINE) != 1:
    sys.exit("template: final theorem line not found")

sub(STMT_LINE[0], "theorem PEqualNP.Outside.{{MOD}} : {{STMT}} := by", 1)
sub("L_meta_12230", "{{MOD}}", t.count("L_meta_12230"))
sub("(reject : search 6 inputs = false)", "(reject : search {{B}} inputs = false)", 1)
sub("    6 < binaryCost gs := by", "    {{B}} < binaryCost gs := by", 1)
sub("have low : binaryCost gs ≤ 6 :=", "have low : binaryCost gs ≤ {{B}} :=", 1)
sub("search_complete ht 6 inputs", "search_complete ht {{B}} inputs", 1)
sub("Nat.testBit 3900762112 (", "Nat.testBit {{F5}} (", 1)
sub(ROWS, "{{ROWS5}}", 1)
sub("theorem reject5 : search 6 rows5 = false", "theorem reject5 : search {{B}} rows5 = false", 1)
sub(": 6 < binaryCost gs :=\n  bound_from_search", ": {{B}} < binaryCost gs :=\n  bound_from_search", 1)
sub("Nat.testBit (3907577984 * 2 ^ 32 + 3907577856) (", "Nat.testBit ({{HI}} * 2 ^ 32 + {{LO}}) (", 1)
sub("insAt (3 : Fin 6) false y", "insAt ({{IDX}} : Fin 6) false y", 1)
sub("drop_one_var (3 : Fin 6) target", "drop_one_var ({{IDX}} : Fin 6) target", 1)
sub("(fun i => (3 : ℕ).testBit i.val) (fun _ => false)",
    "(fun i => ({{YDIFF}} : ℕ).testBit i.val) (fun i => ({{Y0}} : ℕ).testBit i.val)", 1)
sub("(fun i => (11 : ℕ).testBit i.val)", "(fun i => ({{Y1}} : ℕ).testBit i.val)", 1)
sub(WITNESS, "{{WITNESS}}", 1)
sub("have hws : witness.size = 9 := rfl", "have hws : witness.size = {{M}} := rfl", 1)
for k in ("{{MOD}}", "{{STMT}}", "{{B}}", "{{F5}}", "{{ROWS5}}", "{{HI}}", "{{LO}}", "{{IDX}}", "{{YDIFF}}",
          "{{Y0}}", "{{Y1}}", "{{WITNESS}}", "{{M}}"):
    assert k in t, k
# Comments are dropped: pnp.sh check removes them anyway; the credit line is in the generator's header.
open(out, "w", encoding="utf-8").write(t)
print("template written:", out, len(t), "bytes")
