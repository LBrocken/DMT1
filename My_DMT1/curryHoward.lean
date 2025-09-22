#check And
#check Prod

-- (α : Tpye u) (β : Type v) : Type

namespace MyAnd

structure And (a b : Prop) : Prop where
  intro ::
  left : a
  right : b

axiom P : Prop
axiom Q : Prop

def aProof : And P Q := And.intro _ _

#check And.left aProof
#check And.right aProof

end MyAnd

namespace MyProd

structure Prod (α : Type u) (β : Type v) where
  mk ::
  fst : α
  snd : β

#check (Prod)
#check Prod Bool String

def aProd : Prod Bool String := Prod.mk true "I love this stuff!"
#eval aProd
#check Prod.mk

#eval aProd.fst
#eval aProd.snd
end MyProd

namespace MyFuncs

def S : Type := String
def T : Type := Bool

#check S → T

def aFunc : String → Bool :=
  fun (s : String) => false

def aFunc2 : String → Bool :=
  fun (s : String) => true

def x : Nat := 3
def y : Nat := 5

#check ∀ (s : S), T

def aFunc3 : ∀ (s : String), Bool := λ (s : String) => false
-- λ = fun

end MyFuncs

namespace MyOr

#check Bool

inductive Bool : Type where
  | false : Bool
  | true : Bool

def b1 : Bool := Bool.true
def b2 : Bool := Bool.false

#check Or

axiom P : Prop
axiom Q : Prop
axiom p : P

#check Or P Q

theorem pfPorQ : P ∨ Q := --theorem = def
  Or.inl p

theorem pfPorQ2 : P ∨ Q :=

axiom q : Q

theorem pfPorQ2': P ∨ Q := Or.inr q

inductive Or (a b : Prop) : Prop where
  /-- `Or.inl` is "left injection" into an `Or`. If `h : a` then `Or.inl h : a ∨ b`. -/
  | inl (h : a) : Or a b
  /-- `Or.inr` is "right injection" into an `Or`. If `h : b` then `Or.inr h : a ∨ b`. -/
  | inr (h : b) : Or a b


def zeroEqZero : 0 = 0 := rfl

end MyOr

theorem aThm : 0 = 0 ∨ 0 = 1 :=
    let pfZeZ : 0 = 0 := rfl
    Or.inl pfZeZ
