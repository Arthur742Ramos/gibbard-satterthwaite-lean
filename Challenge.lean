import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin

namespace GibbardSatterthwaite

section

variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Nonempty V] [Nonempty A]

def Ballot (A : Type*) : Type _ := { f : A -> ℕ // Function.Injective f }

def ranksAbove (s : Ballot A) (x y : A) : Prop := s.val x < s.val y

def Profile (V A : Type*) : Type _ := V -> Ballot A

/-- A social choice function: assigns a chosen alternative to each ballot profile. -/
def SCF (V A : Type*) : Type _ := Profile V A → A

/-- Strategy-proofness: no voter can get a strictly better outcome (by their own true ballot) by misreporting. -/
def StrategyProof (F : SCF V A) : Prop :=
  ∀ (P : Profile V A) (v : V) (b : Ballot A), ¬ ranksAbove (P v) (F (Function.update P v b)) (F P)

/-- Onto: every alternative is chosen at some profile. -/
def Onto (F : SCF V A) : Prop := Function.Surjective F

/-- Dictatorial: some voter d always gets their top-ranked alternative. -/
def Dictatorial (F : SCF V A) : Prop :=
  ∃ d : V, ∀ (P : Profile V A) (x : A), x ≠ F P → ranksAbove (P d) (F P) x

theorem gibbardSatterthwaite (f : SCF V A) (hSP : StrategyProof f) (hO : Onto f)
    (x y z : A) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : Dictatorial f := by
  sorry

end

end GibbardSatterthwaite
