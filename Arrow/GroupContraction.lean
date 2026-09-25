import Arrow.FieldExpansion
import Mathlib.Data.Finset.Basic

namespace Arrow

section

variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] [Nonempty V]

/-- A decisive coalition of size at least two contains a smaller nonempty decisive
coalition. -/
theorem groupContraction (F : SWF V A) (hU : Unanimous F) (hIIA : IIA F)
    (G : Finset V) (hDec : Decisive F G) (hcard : 2 ≤ G.card)
    (x y z : A) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ G' : Finset V, G' ⊂ G ∧ G'.Nonempty ∧ Decisive F G' := by
  classical
  have hG_nonempty : G.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v₁, hv₁⟩ := hG_nonempty
  let G₁ : Finset V := {v₁}
  let G₂ : Finset V := G \ {v₁}

  have hG₂_nonempty : G₂.Nonempty := by
    by_contra hne
    have hG₂_empty : G₂ = ∅ := by
      apply Finset.ext
      intro v
      constructor
      · intro hv
        exact (hne ⟨v, hv⟩).elim
      · intro hv
        simp at hv
    have hsubset : G ⊆ ({v₁} : Finset V) := by
      intro v hv
      by_cases hv' : v = v₁
      · simp [hv']
      · have hv₂ : v ∈ G₂ := by
          simp [G₂, hv, hv']
        rw [hG₂_empty] at hv₂
        simp at hv₂
    have hcardle : G.card ≤ ({v₁} : Finset V).card := Finset.card_le_card hsubset
    simp at hcardle
    omega

  have hG₁_subset : G₁ ⊆ G := by
    intro v hv
    have hv' : v = v₁ := by simpa [G₁] using hv
    simpa [hv'] using hv₁
  have hG₁_ne : G₁ ≠ G := by
    intro h
    have hcardeq := congrArg Finset.card h
    simp [G₁] at hcardeq
    omega
  have hG₁_ss : G₁ ⊂ G := Finset.ssubset_iff_subset_ne.mpr ⟨hG₁_subset, hG₁_ne⟩

  have hG₂_subset : G₂ ⊆ G := by
    intro v hv
    exact (Finset.mem_sdiff.mp hv).1
  have hG₂_ne : G₂ ≠ G := by
    intro h
    have hv : v₁ ∈ G₂ := h ▸ hv₁
    simp [G₂] at hv
  have hG₂_ss : G₂ ⊂ G := Finset.ssubset_iff_subset_ne.mpr ⟨hG₂_subset, hG₂_ne⟩

  obtain ⟨s_xyz, hxy_xyz, hyz_xyz⟩ := exists_chain x y z hxy hyz hxz
  obtain ⟨s_zxy, hzx_zxy, hxy_zxy⟩ :=
    exists_chain z x y (Ne.symm hxz) hxy (Ne.symm hyz)
  obtain ⟨s_yzx, hyz_yzx, hzx_yzx⟩ :=
    exists_chain y z x hyz (Ne.symm hxz) (Ne.symm hxy)

  let P : Profile V A := fun v =>
    if v ∈ G₁ then s_xyz else if v ∈ G₂ then s_zxy else s_yzx

  have hxyz_xz : ranksAbove s_xyz x z :=
    ranksAbove_trans s_xyz x y z hxy_xyz hyz_xyz
  have hzxy_zy : ranksAbove s_zxy z y :=
    ranksAbove_trans s_zxy z x y hzx_zxy hxy_zxy

  have hPxy : ∀ v ∈ G, ranksAbove (P v) x y := by
    intro v hvG
    by_cases hv : v = v₁
    · subst v
      simpa [P, G₁] using hxy_xyz
    · have hv₁' : v ∉ G₁ := by simpa [G₁] using hv
      have hv₂ : v ∈ G₂ := by simp [G₂, hvG, hv]
      simpa [P, hv₁', hv₂] using hxy_zxy

  have hFxy : ranksAbove (F P) x y := hDec x y hxy P hPxy

  have hP₁xz : ∀ v ∈ G₁, ranksAbove (P v) x z := by
    intro v hv
    have hv' : v = v₁ := by simpa [G₁] using hv
    subst v
    simpa [P, G₁] using hxyz_xz
  have hPout₁zx : ∀ v, v ∉ G₁ → ranksAbove (P v) z x := by
    intro v hv
    by_cases hv₂ : v ∈ G₂
    · simpa [P, hv, hv₂] using hzx_zxy
    · simpa [P, hv, hv₂] using hzx_yzx

  have hP₂zy : ∀ v ∈ G₂, ranksAbove (P v) z y := by
    intro v hv
    have hv₁' : v ∉ G₁ := by
      intro hv₁
      have hv' : v = v₁ := by simpa [G₁] using hv₁
      subst v
      simp [G₂] at hv
    simpa [P, hv₁', hv] using hzxy_zy
  have hPout₂yz : ∀ v, v ∉ G₂ → ranksAbove (P v) y z := by
    intro v hv
    by_cases hv₁ : v ∈ G₁
    · simpa [P, hv₁] using hyz_xyz
    · simpa [P, hv₁, hv] using hyz_yzx

  rcases ranksAbove_trichotomy (F P) y z hyz with hFyz | hFzy
  · have hFxz : ranksAbove (F P) x z :=
      ranksAbove_trans (F P) x y z hFxy hFyz
    have hWD₁ : WeakDecisive F G₁ x z := by
      intro Q hQ₁ hQout₁
      have hAgree : ∀ v, ranksAbove (P v) x z ↔ ranksAbove (Q v) x z := by
        intro v
        by_cases hv : v ∈ G₁
        · have hP := hP₁xz v hv
          have hQ := hQ₁ v hv
          exact ⟨fun _ => hQ, fun _ => hP⟩
        · have hP := hPout₁zx v hv
          have hQ := hQout₁ v hv
          constructor
          · intro h
            exact (ranksAbove_asymm (P v) z x hP h).elim
          · intro h
            exact (ranksAbove_asymm (Q v) z x hQ h).elim
      exact (hIIA P Q x z hAgree).mp hFxz
    have hDec₁ : Decisive F G₁ :=
      fieldExpansion F hU hIIA G₁ x z hxz hWD₁ y hxy (Ne.symm hyz)
    exact ⟨G₁, hG₁_ss, ⟨v₁, by simp [G₁]⟩, hDec₁⟩
  · have hWD₂ : WeakDecisive F G₂ z y := by
      intro Q hQ₂ hQout₂
      have hAgree : ∀ v, ranksAbove (P v) z y ↔ ranksAbove (Q v) z y := by
        intro v
        by_cases hv : v ∈ G₂
        · have hP := hP₂zy v hv
          have hQ := hQ₂ v hv
          exact ⟨fun _ => hQ, fun _ => hP⟩
        · have hP := hPout₂yz v hv
          have hQ := hQout₂ v hv
          constructor
          · intro h
            exact (ranksAbove_asymm (P v) y z hP h).elim
          · intro h
            exact (ranksAbove_asymm (Q v) y z hQ h).elim
      exact (hIIA P Q z y hAgree).mp hFzy
    have hDec₂ : Decisive F G₂ :=
      fieldExpansion F hU hIIA G₂ z y (Ne.symm hyz) hWD₂ x (Ne.symm hxz) (Ne.symm hxy)
    exact ⟨G₂, hG₂_ss, hG₂_nonempty, hDec₂⟩

namespace Palomar

/-- Palomar-facing name for the group contraction lemma. -/
theorem groupContraction (F : SWF V A) (hU : Unanimous F) (hIIA : IIA F)
    (G : Finset V) (hDec : Decisive F G) (hcard : 2 ≤ G.card)
    (x y z : A) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ G' : Finset V, G' ⊂ G ∧ G'.Nonempty ∧ Decisive F G' :=
  Arrow.groupContraction F hU hIIA G hDec hcard x y z hxy hxz hyz

end Palomar

end

end Arrow
