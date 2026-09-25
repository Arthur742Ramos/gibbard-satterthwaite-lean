import GS.Basic

namespace GibbardSatterthwaite

open Arrow

variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] [Nonempty V] [Nonempty A]

private def topTwoScore (s : Ballot A) (x y a : A) : ℕ :=
  if a = x then 0 else if a = y then 1 else s.val a + 2

private theorem profile_update_same (P : Profile V A) (v : V) (b : Ballot A) :
    Function.update (fun w : V => P w) v b v = b := by
  simp [Function.update]

private theorem profile_update_ne (P : Profile V A) (v w : V) (b : Ballot A)
    (hw : w ≠ v) : Function.update (fun z : V => P z) v b w = P w := by
  exact Function.update_of_ne hw b (fun z => P z)

private theorem topTwoScore_injective (s : Ballot A) (x y : A) (hxy : x ≠ y) :
    Function.Injective (topTwoScore s x y) := by
  intro a b hab
  by_cases hax : a = x
  · subst a
    by_cases hbx : b = x
    · exact hbx.symm
    · by_cases hby : b = y
      · subst b
        have heq : (0 : ℕ) = 1 := by
          simpa [topTwoScore, Ne.symm hxy] using hab
        omega
      · have heq : (0 : ℕ) = s.val b + 2 := by
          simpa [topTwoScore, hbx, hby, Ne.symm hxy] using hab
        omega
  · by_cases hay : a = y
    · subst a
      by_cases hbx : b = x
      · subst b
        have heq : (1 : ℕ) = 0 := by
          simpa [topTwoScore, hxy, Ne.symm hxy] using hab
        omega
      · by_cases hby : b = y
        · exact hby.symm
        · have heq : (1 : ℕ) = s.val b + 2 := by
            simpa [topTwoScore, hbx, hby, Ne.symm hxy] using hab
          omega
    · by_cases hbx : b = x
      · subst b
        have heq : s.val a + 2 = 0 := by
          simpa [topTwoScore, hax, hay, hxy] using hab
        omega
      · by_cases hby : b = y
        · subst b
          have heq : s.val a + 2 = 1 := by
            simpa [topTwoScore, hax, hay, hxy, Ne.symm hxy] using hab
          omega
        · have hval : s.val a + 2 = s.val b + 2 := by
            simpa [topTwoScore, hax, hay, hbx, hby] using hab
          have hscore : s.val a = s.val b := by omega
          exact s.property hscore

def topTwoProfile (P : Profile V A) (x y : A) (hxy : x ≠ y) : Profile V A :=
  fun v =>
    haveI : Decidable (ranksAbove (P v) x y) := by
      change Decidable ((P v).val x < (P v).val y)
      infer_instance
    if h : ranksAbove (P v) x y then
      ⟨topTwoScore (P v) x y, topTwoScore_injective (P v) x y hxy⟩
    else
      ⟨topTwoScore (P v) y x, topTwoScore_injective (P v) y x (Ne.symm hxy)⟩

theorem topTwo_preserves (P : Profile V A) (x y : A) (hxy : x ≠ y) (v : V) :
    ranksAbove (topTwoProfile P x y hxy v) x y ↔ ranksAbove (P v) x y := by
  by_cases h : ranksAbove (P v) x y
  · have hx : (topTwoProfile P x y hxy v).val x = 0 := by
      simp [topTwoProfile, h, topTwoScore, hxy, Ne.symm hxy]
    have hy : (topTwoProfile P x y hxy v).val y = 1 := by
      simp [topTwoProfile, h, topTwoScore, hxy, Ne.symm hxy]
    change (topTwoProfile P x y hxy v).val x < (topTwoProfile P x y hxy v).val y ↔
      (P v).val x < (P v).val y
    rw [hx, hy]
    change (P v).val x < (P v).val y at h
    constructor
    · intro _
      exact h
    · intro _
      omega
  · have hx : (topTwoProfile P x y hxy v).val x = 1 := by
      simp [topTwoProfile, h, topTwoScore, hxy, Ne.symm hxy]
    have hy : (topTwoProfile P x y hxy v).val y = 0 := by
      simp [topTwoProfile, h, topTwoScore, hxy, Ne.symm hxy]
    change (topTwoProfile P x y hxy v).val x < (topTwoProfile P x y hxy v).val y ↔
      (P v).val x < (P v).val y
    rw [hx, hy]
    change ¬ ((P v).val x < (P v).val y) at h
    constructor
    · intro hlt
      omega
    · intro hlt
      exact False.elim (h hlt)

theorem topTwo_above_rest (P : Profile V A) (x y : A) (hxy : x ≠ y)
    (v w : V) (z : A) (hzx : z ≠ x) (hzy : z ≠ y) :
    ranksAbove (topTwoProfile P x y hxy v) x z ∧
      ranksAbove (topTwoProfile P x y hxy v) y z := by
  by_cases h : ranksAbove (P v) x y
  · have hx : (topTwoProfile P x y hxy v).val x = 0 := by
      simp [topTwoProfile, h, topTwoScore, hxy, Ne.symm hxy]
    have hy : (topTwoProfile P x y hxy v).val y = 1 := by
      simp [topTwoProfile, h, topTwoScore, hxy, Ne.symm hxy]
    have hz : (topTwoProfile P x y hxy v).val z = (P v).val z + 2 := by
      simp [topTwoProfile, h, topTwoScore, hxy, Ne.symm hxy, hzx, hzy]
    change ((topTwoProfile P x y hxy v).val x < (topTwoProfile P x y hxy v).val z) ∧
      ((topTwoProfile P x y hxy v).val y < (topTwoProfile P x y hxy v).val z)
    rw [hx, hy, hz]
    constructor <;> omega
  · have hx : (topTwoProfile P x y hxy v).val x = 1 := by
      simp [topTwoProfile, h, topTwoScore, hxy, Ne.symm hxy]
    have hy : (topTwoProfile P x y hxy v).val y = 0 := by
      simp [topTwoProfile, h, topTwoScore, hxy, Ne.symm hxy]
    have hz : (topTwoProfile P x y hxy v).val z = (P v).val z + 2 := by
      simp [topTwoProfile, h, topTwoScore, hxy, Ne.symm hxy, hzx, hzy]
    change ((topTwoProfile P x y hxy v).val x < (topTwoProfile P x y hxy v).val z) ∧
      ((topTwoProfile P x y hxy v).val y < (topTwoProfile P x y hxy v).val z)
    rw [hx, hy, hz]
    constructor <;> omega

theorem monotone_one_step (f : SCF V A) (hSP : StrategyProof f) (R R2 : Profile V A)
    (v : V) (x : A)
    (hdiff : ∀ w : V, w ≠ v → R2 w = R w)
    (hfall : ∀ y : A, ranksAbove (R v) x y → ranksAbove (R2 v) x y)
    (hfx : f R = x) : f R2 = x := by
  by_contra hne
  have hRR : Function.update R2 v (R v) = R := by
    have hfun : Function.update (fun w : V => R2 w) v (R v) = R := by
      funext w
      by_cases hw : w = v
      · subst w
        exact profile_update_same R2 v (R v)
      · rw [profile_update_ne R2 v w (R v) hw]
        exact hdiff w hw
    exact hfun
  have hR2R : Function.update R v (R2 v) = R2 := by
    have hfun : Function.update (fun w : V => R w) v (R2 v) = R2 := by
      funext w
      by_cases hw : w = v
      · subst w
        exact profile_update_same R v (R2 v)
      · rw [profile_update_ne R v w (R2 v) hw]
        exact (hdiff w hw).symm
    exact hfun
  have hSP1 : ¬ ranksAbove (R2 v) x (f R2) := by
    have htemp := hSP R2 v (R v)
    rw [hRR, hfx] at htemp
    exact htemp
  have hne2 : x ≠ f R2 := fun heq => hne heq.symm
  rcases ranksAbove_trichotomy (R v) x (f R2) hne2 with hlt | hgt
  · exact hSP1 (hfall (f R2) hlt)
  · have hSP2 : ¬ ranksAbove (R v) (f R2) x := by
      have htemp := hSP R v (R2 v)
      rw [hR2R, hfx] at htemp
      exact htemp
    exact hSP2 hgt

private def morph (R R2 : Profile V A) : List V → Profile V A
  | [] => R
  | v :: vs => Function.update (fun w : V => morph R R2 vs w) v (R2 v)

theorem monotone (f : SCF V A) (hSP : StrategyProof f) (R R2 : Profile V A) (x : A)
    (hfall : ∀ v : V, ∀ y : A, ranksAbove (R v) x y → ranksAbove (R2 v) x y)
    (hfx : f R = x) : f R2 = x := by
  have aux_mem : ∀ (vs : List V) (v : V), v ∈ vs → morph R R2 vs v = R2 v := by
    intro vs
    induction vs with
    | nil =>
        intro v hmem
        simp at hmem
    | cons a as ih =>
        intro v hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with hhead | htail
        · subst v
          exact profile_update_same (morph R R2 as) a (R2 a)
        · by_cases hva : v = a
          · subst v
            exact profile_update_same (morph R R2 as) a (R2 a)
          · change Function.update (fun w : V => morph R R2 as w) a (R2 a) v = R2 v
            rw [profile_update_ne (morph R R2 as) a v (R2 a) hva]
            exact ih v htail
  have aux_either : ∀ (vs : List V) (v : V),
      morph R R2 vs v = R v ∨ morph R R2 vs v = R2 v := by
    intro vs
    induction vs with
    | nil =>
        intro v
        simp [morph]
    | cons a as ih =>
        intro v
        by_cases hva : v = a
        · subst v
          right
          exact profile_update_same (morph R R2 as) a (R2 a)
        · rcases ih v with hR | hR2
          · left
            change Function.update (fun w : V => morph R R2 as w) a (R2 a) v = R v
            rw [profile_update_ne (morph R R2 as) a v (R2 a) hva]
            exact hR
          · right
            change Function.update (fun w : V => morph R R2 as w) a (R2 a) v = R2 v
            rw [profile_update_ne (morph R R2 as) a v (R2 a) hva]
            exact hR2
  have aux_outcome : ∀ (vs : List V), f (morph R R2 vs) = x := by
    intro vs
    induction vs with
    | nil =>
        simpa [morph] using hfx
    | cons v vs ih =>
        have hstep := monotone_one_step f hSP (morph R R2 vs)
          (Function.update (fun w : V => morph R R2 vs w) v (R2 v)) v x
          (fun w hw => profile_update_ne (morph R R2 vs) v w (R2 v) hw)
          (by
            intro y hy
            rw [profile_update_same (morph R R2 vs) v (R2 v)]
            rcases aux_either vs v with hR | hR2
            · rw [hR] at hy
              exact hfall v y hy
            · rw [hR2] at hy
              exact hy)
          ih
        simpa [morph] using hstep
  have hmorph : morph R R2 Finset.univ.toList = R2 := by
    funext v
    apply aux_mem (Finset.univ.toList) v
    exact Finset.mem_toList.mpr (Finset.mem_univ v)
  rw [← hmorph]
  exact aux_outcome Finset.univ.toList

theorem unanimous_of_sp_onto (f : SCF V A) (hSP : StrategyProof f) (hO : Onto f)
    (P : Profile V A) (x : A) (hall : ∀ v : V, topChoice (P v) = x) : f P = x := by
  obtain ⟨Q, hQ⟩ := hO x
  apply monotone f hSP Q P x
  · intro v y hy
    by_cases hyx : y = x
    · subst y
      exact False.elim (ranksAbove_irrefl (Q v) x hy)
    · have htop : topChoice (P v) = x := hall v
      have hneq : y ≠ topChoice (P v) := by
        intro heq
        exact hyx (heq.trans htop)
      simpa [htop] using topChoice_spec (P v) y hneq
  · exact hQ

end GibbardSatterthwaite
