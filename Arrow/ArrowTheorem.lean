import Arrow.GroupContraction
import Mathlib.Data.Finset.Basic

namespace Arrow

section

variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] [Nonempty V]

/-- Under unanimity and independence of irrelevant alternatives, every social welfare
function with at least three alternatives has a dictator. -/
theorem arrowImpossibility (F : SWF V A) (hU : Unanimous F) (hIIA : IIA F)
    (x y z : A) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ d : V, IsDictator F d := by
  classical
  -- The grand coalition is decisive by unanimity.
  have hDecUniv : Decisive F (Finset.univ : Finset V) := fun a b hab =>
    Arrow.Palomar.decisiveUniv F hU a b

  -- Repeatedly contract a non-singleton decisive coalition.
  have key : ∀ n : ℕ, ∀ G : Finset V, G.card = n → G.Nonempty →
      Decisive F G → ∃ d : V, Decisive F ({d} : Finset V) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro G hn hG hDec
      by_cases hOne : n = 1
      · have hGcard : G.card = 1 := by rw [hn, hOne]
        obtain ⟨d, hd⟩ := Finset.card_eq_one.mp hGcard
        refine ⟨d, ?_⟩
        simpa [hd] using hDec
      · have hcardPos : 0 < G.card := Finset.card_pos.mpr hG
        have hcardTwo : 2 ≤ G.card := by omega
        obtain ⟨G', hss, hG'nonempty, hG'dec⟩ :=
          Arrow.groupContraction F hU hIIA G hDec hcardTwo x y z hxy hxz hyz
        have hlt : G'.card < n := by
          rw [← hn]
          exact Finset.card_lt_card hss
        exact ih G'.card hlt G' rfl hG'nonempty hG'dec

  have hUnivNonempty : (Finset.univ : Finset V).Nonempty := by
    obtain ⟨v⟩ := (inferInstance : Nonempty V)
    exact ⟨v, Finset.mem_univ v⟩
  obtain ⟨d, hDecSing⟩ := key (Finset.univ : Finset V).card Finset.univ rfl
    hUnivNonempty hDecUniv

  -- A decisive singleton has the same pairwise ranking as its member.
  refine ⟨d, ?_⟩
  intro P a b
  by_cases hab : a = b
  · subst b
    exact iff_of_false (ranksAbove_irrefl (P d) a) (ranksAbove_irrefl (F P) a)
  · rcases ranksAbove_trichotomy (P d) a b hab with h_ab | h_ba
    · constructor
      · intro hP
        exact hDecSing a b hab P (by
          intro v hv
          have hv' : v = d := Finset.mem_singleton.mp hv
          subst v
          exact hP)
      · intro _
        exact h_ab
    · constructor
      · intro hP
        exact (ranksAbove_asymm (P d) b a h_ba hP).elim
      · intro hF
        have hFba : ranksAbove (F P) b a := hDecSing b a (Ne.symm hab) P (by
          intro v hv
          have hv' : v = d := Finset.mem_singleton.mp hv
          subst v
          exact h_ba)
        exact (ranksAbove_asymm (F P) b a hFba hF).elim

namespace Palomar

theorem arrowImpossibility (F : SWF V A) (hU : Unanimous F) (hIIA : IIA F)
    (x y z : A) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ d : V, IsDictator F d :=
  Arrow.arrowImpossibility F hU hIIA x y z hxy hxz hyz

end Palomar

end

end Arrow
