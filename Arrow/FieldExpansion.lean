import Arrow.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin

namespace Arrow

section

variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] [Nonempty V]

/-- A weakly decisive pair expands to a decisive pair with the same first alternative. -/
theorem weak_expand_left (F : SWF V A) (hU : Unanimous F) (hIIA : IIA F)
    (G : Finset V) (p q r : A)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hWD : WeakDecisive F G p q) : DecisivePair F G p r := by
  classical
  obtain ⟨s_pqr, hpq_pqr, hqr_pqr⟩ := exists_chain p q r hpq hqr hpr
  obtain ⟨s_qpr, hqp_qpr, hpr_qpr⟩ :=
    exists_chain q p r (Ne.symm hpq) hpr hqr
  obtain ⟨s_qrp, hqr_qrp, hrp_qrp⟩ :=
    exists_chain q r p hqr (Ne.symm hpr) (Ne.symm hpq)
  intro Q hQ
  let P : Profile V A := fun v =>
    if v ∈ G then s_pqr
    else if ranksAbove (Q v) p r then s_qpr else s_qrp
  have hFpq : ranksAbove (F P) p q := hWD P
    (by
      intro v hv
      simpa [P, hv] using hpq_pqr)
    (by
      intro v hv
      by_cases hQpr : ranksAbove (Q v) p r
      · simpa [P, hv, hQpr] using hqp_qpr
      · simpa [P, hv, hQpr] using
          ranksAbove_trans s_qrp q r p hqr_qrp hrp_qrp)
  have hAll_qr : ∀ v, ranksAbove (P v) q r := by
    intro v
    by_cases hv : v ∈ G
    · simpa [P, hv] using hqr_pqr
    · by_cases hQpr : ranksAbove (Q v) p r
      · simpa [P, hv, hQpr] using
          ranksAbove_trans s_qpr q p r hqp_qpr hpr_qpr
      · simpa [P, hv, hQpr] using hqr_qrp
  have hFqr : ranksAbove (F P) q r := hU P q r hAll_qr
  have hFpr : ranksAbove (F P) p r :=
    ranksAbove_trans (F P) p q r hFpq hFqr
  have hAgree : ∀ v, ranksAbove (P v) p r ↔ ranksAbove (Q v) p r := by
    intro v
    by_cases hv : v ∈ G
    · have hQpr : ranksAbove (Q v) p r := hQ v hv
      have hPpr : ranksAbove (P v) p r := by
        simpa [P, hv] using ranksAbove_trans s_pqr p q r hpq_pqr hqr_pqr
      exact ⟨fun _ => hQpr, fun _ => hPpr⟩
    · by_cases hQpr : ranksAbove (Q v) p r
      · have hPpr : ranksAbove (P v) p r := by
          simpa [P, hv, hQpr] using hpr_qpr
        exact ⟨fun _ => hQpr, fun _ => hPpr⟩
      · have hrpP : ranksAbove (P v) r p := by
          simpa [P, hv, hQpr] using hrp_qrp
        have hnotP : ¬ ranksAbove (P v) p r :=
          ranksAbove_asymm (P v) r p hrpP
        exact ⟨fun h => (hnotP h).elim, fun h => (hQpr h).elim⟩
  exact (hIIA P Q p r hAgree).mp hFpr

/-- A weakly decisive pair expands to a decisive pair with the same second alternative. -/
theorem weak_expand_right (F : SWF V A) (hU : Unanimous F) (hIIA : IIA F)
    (G : Finset V) (p q r : A)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hWD : WeakDecisive F G p q) : DecisivePair F G r q := by
  classical
  obtain ⟨s_rpq, hrp_rpq, hpq_rpq⟩ :=
    exists_chain r p q (Ne.symm hpr) hpq (Ne.symm hqr)
  obtain ⟨s_rqp, hrq_rqp, hqp_rqp⟩ :=
    exists_chain r q p (Ne.symm hqr) (Ne.symm hpq) (Ne.symm hpr)
  obtain ⟨s_qrp, hqr_qrp, hrp_qrp⟩ :=
    exists_chain q r p hqr (Ne.symm hpr) (Ne.symm hpq)
  intro Q hQ
  let P : Profile V A := fun v =>
    if v ∈ G then s_rpq
    else if ranksAbove (Q v) r q then s_rqp else s_qrp
  have hFpq : ranksAbove (F P) p q := hWD P
    (by
      intro v hv
      simpa [P, hv] using hpq_rpq)
    (by
      intro v hv
      by_cases hQrq : ranksAbove (Q v) r q
      · simpa [P, hv, hQrq] using hqp_rqp
      · simpa [P, hv, hQrq] using
          ranksAbove_trans s_qrp q r p hqr_qrp hrp_qrp)
  have hAll_rp : ∀ v, ranksAbove (P v) r p := by
    intro v
    by_cases hv : v ∈ G
    · simpa [P, hv] using hrp_rpq
    · by_cases hQrq : ranksAbove (Q v) r q
      · simpa [P, hv, hQrq] using
          ranksAbove_trans s_rqp r q p hrq_rqp hqp_rqp
      · simpa [P, hv, hQrq] using hrp_qrp
  have hFrp : ranksAbove (F P) r p := hU P r p hAll_rp
  have hFrq : ranksAbove (F P) r q :=
    ranksAbove_trans (F P) r p q hFrp hFpq
  have hAgree : ∀ v, ranksAbove (P v) r q ↔ ranksAbove (Q v) r q := by
    intro v
    by_cases hv : v ∈ G
    · have hQrq : ranksAbove (Q v) r q := hQ v hv
      have hPrq : ranksAbove (P v) r q := by
        simpa [P, hv] using ranksAbove_trans s_rpq r p q hrp_rpq hpq_rpq
      exact ⟨fun _ => hQrq, fun _ => hPrq⟩
    · by_cases hQrq : ranksAbove (Q v) r q
      · have hPrq : ranksAbove (P v) r q := by
          simpa [P, hv, hQrq] using hrq_rqp
        exact ⟨fun _ => hQrq, fun _ => hPrq⟩
      · have hqrP : ranksAbove (P v) q r := by
          simpa [P, hv, hQrq] using hqr_qrp
        have hnotP : ¬ ranksAbove (P v) r q :=
          ranksAbove_asymm (P v) q r hqrP
        exact ⟨fun h => (hnotP h).elim, fun h => (hQrq h).elim⟩
  exact (hIIA P Q r q hAgree).mp hFrq

/-- The pair on which a coalition is weakly decisive is itself decisive. -/
theorem weak_expand_same (F : SWF V A) (hU : Unanimous F) (hIIA : IIA F)
    (G : Finset V) (p q r : A)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hWD : WeakDecisive F G p q) : DecisivePair F G p q := by
  have hprD : DecisivePair F G p r :=
    weak_expand_left F hU hIIA G p q r hpq hpr hqr hWD
  have hrqD : DecisivePair F G r q :=
    weak_expand_right F hU hIIA G p q r hpq hpr hqr hWD
  obtain ⟨s_prq, hpr_prq, hrq_prq⟩ := exists_chain p r q hpr (Ne.symm hqr) hpq
  intro Q hQ
  let P : Profile V A := fun v => if v ∈ G then s_prq else Q v
  have hFpr : ranksAbove (F P) p r := hprD P (by
    intro v hv
    simpa [P, hv] using hpr_prq)
  have hFrq : ranksAbove (F P) r q := hrqD P (by
    intro v hv
    simpa [P, hv] using hrq_prq)
  have hFpq : ranksAbove (F P) p q :=
    ranksAbove_trans (F P) p r q hFpr hFrq
  have hAgree : ∀ v, ranksAbove (P v) p q ↔ ranksAbove (Q v) p q := by
    intro v
    by_cases hv : v ∈ G
    · have hQpq : ranksAbove (Q v) p q := hQ v hv
      have hPpq : ranksAbove (P v) p q := by
        simpa [P, hv] using ranksAbove_trans s_prq p r q hpr_prq hrq_prq
      exact ⟨fun _ => hQpq, fun _ => hPpq⟩
    · simp [P, hv]
  exact (hIIA P Q p q hAgree).mp hFpq

/-- A weakly decisive coalition is decisive for every ordered pair of alternatives. -/
theorem fieldExpansion (F : SWF V A) (hU : Unanimous F) (hIIA : IIA F)
    (G : Finset V) (x y : A) (hxy : x ≠ y) (hWD : WeakDecisive F G x y)
    (z : A) (hxz : x ≠ z) (hyz : y ≠ z) : Decisive F G := by
  have hxyD : DecisivePair F G x y :=
    weak_expand_same F hU hIIA G x y z hxy hxz hyz hWD
  have hxzD : DecisivePair F G x z :=
    weak_expand_left F hU hIIA G x y z hxy hxz hyz hWD
  have hyzD : DecisivePair F G y z := by
    have hxzW : WeakDecisive F G x z := weakOfDecisivePair F G x z hxzD
    exact weak_expand_right F hU hIIA G x z y hxz hxy (Ne.symm hyz) hxzW
  intro a b hab
  by_cases hay : a = y
  · subst a
    by_cases hbz : b = z
    · subst b
      exact hyzD
    · have hyzW : WeakDecisive F G y z := weakOfDecisivePair F G y z hyzD
      exact weak_expand_left F hU hIIA G y z b hyz hab (Ne.symm hbz) hyzW
  · have hayD : DecisivePair F G a y := by
      by_cases hax : a = x
      · subst a
        exact hxyD
      · exact weak_expand_right F hU hIIA G x y a hxy (Ne.symm hax)
          (Ne.symm hay) hWD
    by_cases hby : b = y
    · subst b
      exact hayD
    · have hayW : WeakDecisive F G a y :=
        weakOfDecisivePair F G a y hayD
      exact weak_expand_left F hU hIIA G a y b hay hab (Ne.symm hby) hayW

namespace Palomar

/-- Palomar-facing name for the field expansion lemma. -/
theorem fieldExpansion (F : SWF V A) (hU : Unanimous F) (hIIA : IIA F)
    (G : Finset V) (x y : A) (hxy : x ≠ y) (hWD : WeakDecisive F G x y)
    (z : A) (hxz : x ≠ z) (hyz : y ≠ z) : Decisive F G :=
  Arrow.fieldExpansion F hU hIIA G x y hxy hWD z hxz hyz

end Palomar

end

end Arrow
