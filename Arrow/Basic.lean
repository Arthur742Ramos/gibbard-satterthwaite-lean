import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin

namespace Arrow

section

variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] [Nonempty V]

def Ballot (A : Type*) : Type _ := { f : A -> ℕ // Function.Injective f }

def ranksAbove (s : Ballot A) (x y : A) : Prop := s.val x < s.val y

def Profile (V A : Type*) : Type _ := V -> Ballot A

def SWF (V A : Type*) : Type _ := Profile V A -> Ballot A

def Unanimous (F : SWF V A) : Prop := ∀ (P : Profile V A) (x y : A), (∀ v, ranksAbove (P v) x y) -> ranksAbove (F P) x y

def IIA (F : SWF V A) : Prop := ∀ (P Q : Profile V A) (x y : A), (∀ v, (ranksAbove (P v) x y ↔ ranksAbove (Q v) x y)) -> (ranksAbove (F P) x y ↔ ranksAbove (F Q) x y)

def WeakDecisive (F : SWF V A) (G : Finset V) (x y : A) : Prop := ∀ P : Profile V A, (∀ v ∈ G, ranksAbove (P v) x y) -> (∀ v ∉ G, ranksAbove (P v) y x) -> ranksAbove (F P) x y

def DecisivePair (F : SWF V A) (G : Finset V) (x y : A) : Prop := ∀ P : Profile V A, (∀ v ∈ G, ranksAbove (P v) x y) -> ranksAbove (F P) x y

def Decisive (F : SWF V A) (G : Finset V) : Prop := ∀ x y : A, x ≠ y -> DecisivePair F G x y

def IsDictator (F : SWF V A) (d : V) : Prop := ∀ (P : Profile V A) (x y : A), (ranksAbove (P d) x y ↔ ranksAbove (F P) x y)

noncomputable def chainFun (f0 : A -> ℕ) (x y z w : A) : ℕ :=
  if w = x then 0 else if w = y then 1 else if w = z then 2 else 3 * f0 w + 3

theorem chainFun_injective (f0 : A -> ℕ) (hf0 : Function.Injective f0)
    (x y z : A) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    Function.Injective (chainFun f0 x y z) := by
  have h0 : ∀ w : A, chainFun f0 x y z w = 0 -> w = x := by
    intro w hw
    by_cases hwx : w = x
    · exact hwx
    · by_cases hwy : w = y
      · subst w
        simp [chainFun, Ne.symm hxy] at hw
      · by_cases hwz : w = z
        · subst w
          simp [chainFun, Ne.symm hxz, Ne.symm hyz] at hw
        · simp [chainFun, hwx, hwy, hwz] at hw
  have h1 : ∀ w : A, chainFun f0 x y z w = 1 -> w = y := by
    intro w hw
    by_cases hwx : w = x
    · subst w
      simp [chainFun] at hw
    · by_cases hwy : w = y
      · exact hwy
      · by_cases hwz : w = z
        · subst w
          simp [chainFun, Ne.symm hxz, Ne.symm hyz] at hw
        · simp [chainFun, hwx, hwy, hwz] at hw
  have h2 : ∀ w : A, chainFun f0 x y z w = 2 -> w = z := by
    intro w hw
    by_cases hwx : w = x
    · subst w
      simp [chainFun] at hw
    · by_cases hwy : w = y
      · subst w
        simp [chainFun, Ne.symm hxy] at hw
      · by_cases hwz : w = z
        · exact hwz
        · simp [chainFun, hwx, hwy, hwz] at hw
  have h3 : ∀ w : A, 3 ≤ chainFun f0 x y z w ->
      w ≠ x ∧ w ≠ y ∧ w ≠ z ∧ chainFun f0 x y z w = 3 * f0 w + 3 := by
    intro w hw
    by_cases hwx : w = x
    · subst w
      simp [chainFun] at hw
    · by_cases hwy : w = y
      · subst w
        simp [chainFun, Ne.symm hxy] at hw
      · by_cases hwz : w = z
        · subst w
          simp [chainFun, Ne.symm hxz, Ne.symm hyz] at hw
        · exact ⟨hwx, hwy, hwz, by simp [chainFun, hwx, hwy, hwz]⟩
  intro a b hab
  have hcl : chainFun f0 x y z a = 0 ∨ chainFun f0 x y z a = 1 ∨
      chainFun f0 x y z a = 2 ∨ 3 ≤ chainFun f0 x y z a := by
    unfold chainFun
    split_ifs with h1 h2 h3 <;> omega
  rcases hcl with ha | ha | ha | ha
  · exact (h0 a ha).trans (h0 b (ha ▸ hab.symm)).symm
  · exact (h1 a ha).trans (h1 b (ha ▸ hab.symm)).symm
  · exact (h2 a ha).trans (h2 b (ha ▸ hab.symm)).symm
  · obtain ⟨hax, hay, haz, haeq⟩ := h3 a ha
    have hb : 3 ≤ chainFun f0 x y z b := hab ▸ ha
    obtain ⟨hbx, hby, hbz, hbeq⟩ := h3 b hb
    have hformula : 3 * f0 a + 3 = 3 * f0 b + 3 := haeq.symm.trans (hab.trans hbeq)
    have hscaled : 3 * f0 a = 3 * f0 b := Nat.add_right_cancel hformula
    have hfab : f0 a = f0 b := by omega
    exact hf0 hfab

theorem ranksAbove_irrefl (s : Ballot A) (x : A) : ¬ ranksAbove s x x := fun h => Nat.lt_irrefl _ h

theorem ranksAbove_trans (s : Ballot A) (x y z : A) : ranksAbove s x y -> ranksAbove s y z -> ranksAbove s x z := fun h1 h2 => Nat.lt_trans h1 h2

theorem ranksAbove_asymm (s : Ballot A) (x y : A) : ranksAbove s x y -> ¬ ranksAbove s y x := fun h1 h2 => Nat.lt_asymm h1 h2

theorem ranksAbove_trichotomy (s : Ballot A) (x y : A) (hxy : x ≠ y) : ranksAbove s x y ∨ ranksAbove s y x := by
  have hne : s.val x ≠ s.val y := fun heq => hxy (s.property heq)
  exact lt_or_gt_of_ne hne

theorem exists_third (h3 : ∃ a b c : A, a ≠ b ∧ a ≠ c ∧ b ≠ c) (p q : A) (hpq : p ≠ q) :
    ∃ r : A, r ≠ p ∧ r ≠ q := by
  obtain ⟨t1, t2, t3, h12, h13, h23⟩ := h3
  by_contra hcon
  have hmem : ∀ r : A, r = p ∨ r = q := by
    intro r
    by_contra hr
    exact hcon ⟨r, fun heq => hr (Or.inl heq), fun heq => hr (Or.inr heq)⟩
  rcases hmem t1 with rfl | rfl <;> rcases hmem t2 with rfl | rfl <;>
    rcases hmem t3 with rfl | rfl <;>
    first | exact (h12 rfl).elim | exact (h13 rfl).elim | exact (h23 rfl).elim

theorem exists_chain (x y z : A) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    ∃ s : Ballot A, ranksAbove s x y ∧ ranksAbove s y z := by
  classical
  let f0 : A -> ℕ := fun a => (Fintype.equivFin A a).val
  have hf0 : Function.Injective f0 := fun a b hab => (Fintype.equivFin A).injective (Fin.val_inj.mp (by simpa [f0] using hab))
  refine ⟨⟨chainFun f0 x y z, chainFun_injective f0 hf0 x y z hxy hyz hxz⟩, ?_, ?_⟩
  · show chainFun f0 x y z x < chainFun f0 x y z y
    have e1 : chainFun f0 x y z x = 0 := by unfold chainFun; simp
    have e2 : chainFun f0 x y z y = 1 := by unfold chainFun; simp [Ne.symm hxy]
    rw [e1, e2]
    omega
  · show chainFun f0 x y z y < chainFun f0 x y z z
    have e2 : chainFun f0 x y z y = 1 := by unfold chainFun; simp [Ne.symm hxy]
    have e3 : chainFun f0 x y z z = 2 := by unfold chainFun; simp [Ne.symm hxz, Ne.symm hyz]
    rw [e2, e3]
    omega

theorem weakOfDecisivePair (F : SWF V A) (G : Finset V) (x y : A) :
    DecisivePair F G x y -> WeakDecisive F G x y :=
  fun hDP P hP _ => hDP P hP

namespace Palomar

theorem decisiveUniv (F : SWF V A) (hU : Unanimous F) (x y : A) :
    DecisivePair F Finset.univ x y := by
  intro P hP
  by_cases hxy : x = y
  · subst hxy
    obtain ⟨v0⟩ := (inferInstance : Nonempty V)
    exact False.elim (ranksAbove_irrefl (P v0) x (hP v0 (Finset.mem_univ v0)))
  · exact hU P x y (fun v => hP v (Finset.mem_univ v))

end Palomar

end

end Arrow
