/- @@@
#1. Suppose P and Q are any propositions.

#1.A: State and prove the conjecture that,
*and* implies *equivalence*. In other words,
if for any propositions, X and Y, X ∧ Y is
true, then it must be that X ↔ Y is as well.
Call your theorem andImpEquiv.
@@@ -/


theorem andImpEquiv (P Q : Prop) : (P ∧ Q) → (P ↔ Q) :=
  fun h_and : P ∧ Q =>
    Iff.intro (fun h_p : P =>
        And.right h_and)
      (fun h_q : Q =>
        And.left h_and)


/- @@@
#2: Give the proof in #1 in English. To do this,
just explain clearly what assumptions you make or
use at each step and what inference rules you use
to make progress at each step. We get you started:

-- ANSWER
Proof: To prove this *implication* we'll use the
introduction rule for →. So *assume* the premise
is true. What remains to be proved is that, in this
context,  and we will then show that, in that
context, the conclusion must be true as well. So
assume P ∧ Q is true. The conclusion to be proved
is an equivalence. To prove an equivalence we need
to prove both implications, which means we have to
prove it works both ways. To prove P → Q, let's
assume P is true. Our main starting assumption
-- was that P ∧ Q is true. If "P and Q" are both
true, then Q has to be true. Therefore, P → Q. To
prove Q → P, we can use the same logic. Let's assume
Q is true. Going back to our main assumption of P ∧ Q,
this means P must also be true, showing that Q → P.
@@@ -/


/- @@@
#3: Use axiom declarations to represent this world.

- X is a proposition
- Y is a proposition
- X ∧ Y is true

Once you've done that, in a #check command, apply
the general theorem we just proved to prove that X
is equivalent to Y.

Do not just copy the proof. The whole point is to
reinforce the idea that one you've proved a theorem
you can use it (by applying it) to prove any special
case (here involving X and Y) of the general claim.
@@@ -/

axiom X : Prop
axiom Y : Prop
axiom h_xy_and : X ∧ Y

#check (andImpEquiv X Y h_xy_and)

/- @@@
#4: Something About False

Recall from class discussion that the proposition,
in Lean, called False, has no proofs at all. That
is what makes it false. Assuming that there is one
assumes something that's impossibile. The crucial
conclusion to draw is *not* that the impossible is
suddenly possible, but that the *assumption* itself
must be wrong. Therefore, if at any point in trying
to prove something we can derive a proof of False,
that means we're in a situation that can't actually
happen. So we really don't have to finish the proof!

For example, suppose  K is some unknown proposition.
When we say that (False → K) is true, we are *not*
saying that *K* is true; we're saying that once you
assume or can derive a proof of False, you know you
are in a case that can never happen, so you can just
"bail out" and not worry about constructing a proof
of K, no matter what proposition it is. The keyword
*nomatch* in Lean applied to any proof of false does
exactly bail one of of an impossible case.

Here's a formal proof of it. We assume K is any
proposition, then we prove False → K. To prove
this implication, we assume we're given f, a proof
of false. In any other situation, for *exFalsoK*
to be defined, we'd *have to* return some value of
type K. Here we don't even know what that type is.
And yet the function is well-defined, and as such
*proves* the implication, *False → K*. The trick
of course, is that as soon as we have a proof of
false in (or derivable given) our context, then we
can *bail out* and Lean will accept the definition.
Lean's *nomatch* contruct will bail you out as long
as it's applied to a proof of false, which is the
evidence Lean needs to know it's ok to accept the
definition.
@@@ -/

-- ANSWER


/- @@@
Why is it safe to accept tihs definition? What do we
know that's special about *exFalsoK* that makes it ok?

It's safe to accept this definition because the
function "exFalsoK" can never actually be called.
The function requires you to give it a proof that
an impossible event (false) happened. Since you can
never provide a proof of False, this function can
never run. Since it's logically impossible, the
definition is accepted.

@@@ -/


/- @@@
#5 In Lean, state and prove the proposition that is
P and Q are aribtrary propositions, then False *and*
P implies Q.
@@@-/

theorem falseAndImpliesQ (P Q : Prop) : (False ∧ P) → Q :=
  fun h_false_and_p : False ∧ P =>
    False.elim (And.left h_false_and_p)

/- @@@
Write a short paragraph stating the proposition to be
proved and the proof of it -- in English.
@@@ -/

/-
To prove that for any propositions P and Q, the statement
"False ∧ P" implies "Q", you must assume the first part
(False ∧ P) is true. If the statement is true, it means
both parts must be true individually, which is a problem
because the False proposition can never be true. This
creates a contradiction, which means that we can claim
any proposition as true now, since the logical system is
broken. Since our assumption led us to a contradiction,
this rule lets us conclude that Q is true.
-/


/- @@@
#6 State and prove the proposition that False → False.
Give both formal and English (natural language) proofs.
@@@ -/


--Formal Proof
theorem false_imp_false : False → False :=
  fun h_false : False =>
    h_false

/-English Proof
To proof the proposition "False → False", let's assume
the "if" part (False) is true. Using this, we must prove
the "then" part (also False). Since our assumption is the
same as the thing we're trying to prove, the proof is
complete because assuming the premise immediately gives us
the conclusion.
-/
