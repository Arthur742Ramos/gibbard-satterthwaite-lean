import Arrow.Basic

namespace GibbardSatterthwaite

section

variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] [Nonempty V]

open Arrow

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

/-- If d is a dictator and x is ranked above the outcome in d's ballot, x must be the outcome. -/
theorem dictator_top (F : SCF V A) (d : V)
    (hd : ∀ (P : Profile V A) (x : A), x ≠ F P → ranksAbove (P d) (F P) x)
    (P : Profile V A) (x : A) (h : ranksAbove (P d) x (F P)) : x = F P := by
  by_contra hne
  exact ranksAbove_asymm (P d) (F P) x (hd P x hne) h

/-- A dictator's uniquely-top alternative is the outcome: if y is top of d's ballot then y = F P. -/
theorem top_of_dictator (F : SCF V A) (d : V)
    (hd : ∀ (P : Profile V A) (x : A), x ≠ F P → ranksAbove (P d) (F P) x)
    (P : Profile V A) (y : A) (hy : ∀ x : A, x ≠ y → ranksAbove (P d) y x) : y = F P := by
  by_contra hne
  have h1 : ranksAbove (P d) (F P) y := hd P y hne
  have h2 : ranksAbove (P d) y (F P) := hy (F P) (Ne.symm hne)
  exact ranksAbove_asymm (P d) (F P) y h1 h2

variable [Nonempty A]

private theorem exists_min_rank (s : Ballot A) :
    ∃ x : A, ∀ y : A, s.val x ≤ s.val y := by
  classical
  let p : ℕ → Prop := fun n => ∃ x : A, s.val x = n
  have hp : ∃ n, p n := by
    obtain ⟨a⟩ := (inferInstance : Nonempty A)
    exact ⟨s.val a, ⟨a, rfl⟩⟩
  obtain ⟨x, hx⟩ := Nat.find_spec hp
  refine ⟨x, ?_⟩
  intro y
  have hmin : Nat.find hp ≤ s.val y :=
    Nat.find_min' hp ⟨y, rfl⟩
  change s.val x ≤ s.val y
  rw [hx]
  exact hmin

/-- The uniquely top-ranked alternative of a ballot, chosen by minimizing its score. -/
noncomputable def topChoice (s : Ballot A) : A :=
  Classical.choose (exists_min_rank s)

/-- The top choice is ranked strictly above every other alternative. -/
theorem topChoice_spec (s : Ballot A) (x : A)
    (hx : x ≠ topChoice s) : ranksAbove s (topChoice s) x := by
  have hmin := Classical.choose_spec (exists_min_rank s)
  have hle : s.val (topChoice s) ≤ s.val x := hmin x
  have hne : s.val (topChoice s) ≠ s.val x := by
    intro heq
    exact (Ne.symm hx) (s.property heq)
  change s.val (topChoice s) < s.val x
  omega

/-- Any alternative ranked above all others is the top choice. -/
theorem topChoice_unique (s : Ballot A) (y : A)
    (hy : ∀ x : A, x ≠ y → ranksAbove s y x) : y = topChoice s := by
  by_contra hne
  have h1 : ranksAbove s (topChoice s) y := topChoice_spec s y hne
  have h2 : ranksAbove s y (topChoice s) := hy (topChoice s) (Ne.symm hne)
  exact ranksAbove_asymm s (topChoice s) y h1 h2

end

end GibbardSatterthwaite
