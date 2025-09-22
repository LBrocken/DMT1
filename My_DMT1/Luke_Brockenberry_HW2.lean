/-
IMPORTANT: I don't think I understand how to find the instructions for HWs.

When writing this program, I went off the statement in the "announcements" tab
saying that we must "write two quick proofs involving And propositions", as the assignment
on Canvas didn't say anything about the instructions for this assignment.

The Canvas details said to add a statement of confusion if you're lost. This is my statement.

If the announcement was referring to two SPECIFIC proofs specified in a HW#2 instructions
page somewhere, I'm sorry for not following that. If you could reach out to me and explain
how to view our homework assignment instructions, that would be greatly appreciated.
-/

axiom P: Prop
axiom Q: Prop

axiom pq : P ∧ Q

#check pq

def Z : Prop := P ∧ Q → Q ∧ P

def z : Z :=
  fun (pq : P ∧ Q) =>
  And.intro (pq.right) (pq.left)

#check z pq
