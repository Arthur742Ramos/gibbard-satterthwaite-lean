import GS.SWF
import Arrow.ArrowTheorem

namespace GibbardSatterthwaite

open Arrow

variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Nonempty V] [Nonempty A]

theorem beats_of_unanimous (f : SCF V A) (hSP : StrategyProof f) (hO : Onto f)
    (P : Profile V A) (x y : A) (hxy : x ≠ y)
    (h : ∀ v : V, ranksAbove (P v) x y) : beats f P x y := by
  let T : Profile V A := topTwoProfile P x y hxy
  let R : Profile V A := fun v => xTopBallot (T v) x
  have hfx : f R = x :=
    unanimous_of_sp_onto f hSP hO R x (fun v => xTopBallot_top (T v) x)
  have hfall : ∀ v w, ranksAbove (R v) x w → ranksAbove (T v) x w := by
    intro v w hw
    by_cases hwx : w = x
    · subst w
      exact False.elim (ranksAbove_irrefl (R v) x hw)
    · by_cases hwy : w = y
      · subst w
        exact (topTwo_preserves P x y hxy v).mpr (h v)
      · exact (topTwo_above_rest P x y hxy v v w hwx hwy).1
  have hTx : f T = x := monotone f hSP R T x hfall hfx
  exact ⟨hxy, hTx⟩

theorem swfOfSCF_unanimous (f : SCF V A) (hSP : StrategyProof f) (hO : Onto f) :
    Unanimous (swfOfSCF f hSP hO) := by
  intro P x y h
  by_cases hxy : x = y
  · subst y
    obtain ⟨v0⟩ := (inferInstance : Nonempty V)
    exact False.elim (ranksAbove_irrefl (P v0) x (h v0))
  · rw [swfOfSCF_spec f hSP hO P x y hxy]
    exact beats_of_unanimous f hSP hO P x y hxy h

theorem swfOfSCF_IIA (f : SCF V A) (hSP : StrategyProof f) (hO : Onto f) :
    IIA (swfOfSCF f hSP hO) := by
  intro P Q x y hagree
  by_cases hxy : x = y
  · subst y
    exact iff_of_false
      (ranksAbove_irrefl (swfOfSCF f hSP hO P) x)
      (ranksAbove_irrefl (swfOfSCF f hSP hO Q) x)
  · rw [swfOfSCF_spec f hSP hO P x y hxy,
      swfOfSCF_spec f hSP hO Q x y hxy]
    exact pairwise_IIA f hSP P Q x y hxy hagree

theorem gibbardSatterthwaite (f : SCF V A) (hSP : StrategyProof f) (hO : Onto f)
    (x y z : A) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : Dictatorial f := by
  obtain ⟨d, hd⟩ := arrowImpossibility (swfOfSCF f hSP hO)
    (swfOfSCF_unanimous f hSP hO) (swfOfSCF_IIA f hSP hO) x y z hxy hxz hyz
  refine ⟨d, fun P w hw => ?_⟩
  by_contra hcon
  have hwf : w ≠ f P := hw
  rcases ranksAbove_trichotomy (P d) w (f P) hwf with hwd | hdw
  · have hsw := (hd P w (f P)).mp hwd
    rw [swfOfSCF_spec f hSP hO P w (f P) hwf] at hsw
    have htop : f (topTwoProfile P w (f P) hwf) = w := by
      obtain ⟨_, e⟩ := hsw
      exact e
    have hfall : ∀ v u, ranksAbove (P v) (f P) u →
        ranksAbove (topTwoProfile P w (f P) hwf v) (f P) u := by
      intro v u hu
      by_cases huf : u = f P
      · subst u
        exact False.elim (ranksAbove_irrefl (P v) (f P) hu)
      · by_cases huw : u = w
        · subst u
          exact (topTwo_preserves_flip P w (f P) hwf v).mpr hu
        · exact (topTwo_above_rest P w (f P) hwf v v u huw huf).2
    have hTP : f (topTwoProfile P w (f P) hwf) = f P :=
      monotone f hSP P _ (f P) hfall rfl
    rw [htop] at hTP
    exact hwf hTP
  · exact hcon hdw

end GibbardSatterthwaite
