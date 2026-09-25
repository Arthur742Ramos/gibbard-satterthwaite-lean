import GS.Reduction

namespace GibbardSatterthwaite

open Arrow

variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Nonempty V] [Nonempty A]

private def xTopScore (s : Ballot A) (x a : A) : ℕ :=
  if a = x then 0 else s.val a + 1

private theorem xTopScore_injective (s : Ballot A) (x : A) :
    Function.Injective (xTopScore s x) := by
  intro a b hab
  by_cases hax : a = x
  · subst a
    by_cases hbx : b = x
    · exact hbx.symm
    · have heq : (0 : ℕ) = s.val b + 1 := by
        simpa [xTopScore, hbx] using hab
      omega
  · by_cases hbx : b = x
    · subst b
      have heq : s.val a + 1 = 0 := by
        simpa [xTopScore, hax] using hab
      omega
    · have heq : s.val a + 1 = s.val b + 1 := by
        simpa [xTopScore, hax, hbx] using hab
      have hval : s.val a = s.val b := by omega
      exact s.property hval

def xTopBallot (s : Ballot A) (x : A) : Ballot A :=
  ⟨xTopScore s x, xTopScore_injective s x⟩

theorem xTopBallot_top (s : Ballot A) (x : A) :
    topChoice (xTopBallot s x) = x := by
  apply (topChoice_unique (xTopBallot s x) x ?_).symm
  intro w hw
  change (xTopBallot s x).val x < (xTopBallot s x).val w
  simp [xTopBallot, xTopScore, hw]

theorem topTwo_range (f : SCF V A) (hSP : StrategyProof f) (hO : Onto f)
    (P : Profile V A) (x y : A) (hxy : x ≠ y) :
    f (topTwoProfile P x y hxy) = x ∨ f (topTwoProfile P x y hxy) = y := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hnx, hny⟩ := hcon
  let S := topTwoProfile P x y hxy
  let z := f S
  have hzx : z ≠ x := hnx
  have hzy : z ≠ y := hny
  let R2 : Profile V A := fun v => xTopBallot (S v) x
  have hfall : ∀ (v : V) (w : A), ranksAbove (S v) z w → ranksAbove (R2 v) z w := by
    intro v w hw
    have e1 : (R2 v).val z = (S v).val z + 1 := by
      simp [R2, xTopBallot, xTopScore, hzx]
    by_cases hwx : w = x
    · subst w
      have hab := (topTwo_above_rest P x y hxy v v z hzx hzy).1
      change (S v).val x < (S v).val z at hab
      change (S v).val z < (S v).val x at hw
      omega
    · have e2 : (R2 v).val w = (S v).val w + 1 := by
        simp [R2, xTopBallot, xTopScore, hwx]
      change (R2 v).val z < (R2 v).val w
      rw [e1, e2]
      change (S v).val z < (S v).val w at hw
      omega
  have hfz : f R2 = z := monotone f hSP S R2 z hfall rfl
  have hfx : f R2 = x := unanimous_of_sp_onto f hSP hO R2 x (fun v => xTopBallot_top (S v) x)
  exact hzx (hfz.symm.trans hfx)

private theorem predCount_lt {a b c : ℕ} (hab : a ≠ b) :
    ((if b < a then 1 else 0) + (if c < a then 1 else 0) <
      (if a < b then 1 else 0) + (if c < b then 1 else 0)) ↔ a < b := by
  by_cases h : a < b <;> by_cases h2 : b < a <;> by_cases c1 : c < a <;>
    by_cases c2 : c < b <;> simp [h, h2, c1, c2] <;> omega

private def threeTopScore (s : Ballot A) (x y z a : A) : ℕ :=
  if a = x then (if s.val y < s.val x then 1 else 0) + (if s.val z < s.val x then 1 else 0)
  else if a = y then (if s.val x < s.val y then 1 else 0) + (if s.val z < s.val y then 1 else 0)
  else if a = z then (if s.val x < s.val z then 1 else 0) + (if s.val y < s.val z then 1 else 0)
  else s.val a + 3

private theorem threeTopScore_injective (s : Ballot A) (x y z : A)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    Function.Injective (threeTopScore s x y z) := by
  intro a b hab
  let sc := threeTopScore s x y z
  have hxyv : s.val x ≠ s.val y := fun he => hxy (s.property he)
  have hyzv : s.val y ≠ s.val z := fun he => hyz (s.property he)
  have hxzv : s.val x ≠ s.val z := fun he => hxz (s.property he)
  have hscoreX : sc x = (if s.val y < s.val x then 1 else 0) +
      (if s.val z < s.val x then 1 else 0) := by
    simp [sc, threeTopScore, hxy, Ne.symm hxy, hxz, Ne.symm hxz]
  have hscoreY : sc y = (if s.val x < s.val y then 1 else 0) +
      (if s.val z < s.val y then 1 else 0) := by
    simp [sc, threeTopScore, hxy, Ne.symm hxy, hyz, Ne.symm hyz]
  have hscoreZ : sc z = (if s.val x < s.val z then 1 else 0) +
      (if s.val y < s.val z then 1 else 0) := by
    simp [sc, threeTopScore, hxz, Ne.symm hxz, hyz, Ne.symm hyz]
  have hscxy : sc x ≠ sc y := by
    intro he
    by_cases h : s.val x < s.val y
    · have hs : sc x < sc y := by
        rw [hscoreX, hscoreY]
        have hc := (predCount_lt (a := s.val x) (b := s.val y) (c := s.val z) hxyv).2 h
        omega
      omega
    · have h' : s.val y < s.val x := by omega
      have hs : sc y < sc x := by
        rw [hscoreY, hscoreX]
        have hc := (predCount_lt (a := s.val y) (b := s.val x) (c := s.val z)
          (Ne.symm hxyv)).2 h'
        omega
      omega
  have hscyz : sc y ≠ sc z := by
    intro he
    by_cases h : s.val y < s.val z
    · have hs : sc y < sc z := by
        rw [hscoreY, hscoreZ]
        have hc := (predCount_lt (a := s.val y) (b := s.val z) (c := s.val x) hyzv).2 h
        omega
      omega
    · have h' : s.val z < s.val y := by omega
      have hs : sc z < sc y := by
        rw [hscoreZ, hscoreY]
        have hc := (predCount_lt (a := s.val z) (b := s.val y) (c := s.val x)
          (Ne.symm hyzv)).2 h'
        omega
      omega
  have hscxz : sc x ≠ sc z := by
    intro he
    by_cases h : s.val x < s.val z
    · have hs : sc x < sc z := by
        rw [hscoreX, hscoreZ]
        have hc := (predCount_lt (a := s.val x) (b := s.val z) (c := s.val y) hxzv).2 h
        omega
      omega
    · have h' : s.val z < s.val x := by omega
      have hs : sc z < sc x := by
        rw [hscoreZ, hscoreX]
        have hc := (predCount_lt (a := s.val z) (b := s.val x) (c := s.val y)
          (Ne.symm hxzv)).2 h'
        omega
      omega
  have bound (w : A) (hw : w = x ∨ w = y ∨ w = z) : sc w ≤ 2 := by
    rcases hw with hwx | hwy | hwz
    · subst w
      rw [hscoreX]
      split_ifs <;> omega
    · subst w
      rw [hscoreY]
      split_ifs <;> omega
    · subst w
      rw [hscoreZ]
      split_ifs <;> omega
  have rest (w : A) (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z) :
      sc w = s.val w + 3 := by
    simp [sc, threeTopScore, hwx, hwy, hwz]
  by_cases hax : a = x
  · subst a
    by_cases hbx : b = x
    · subst b
      rfl
    · by_cases hby : b = y
      · subst b
        exact False.elim (hscxy (by simpa [sc] using hab))
      · by_cases hbz : b = z
        · subst b
          exact False.elim (hscxz (by change sc x = sc z at hab; exact hab))
        · have hr : sc b = s.val b + 3 := rest b hbx hby hbz
          change sc x = sc b at hab
          rw [hr] at hab
          have ha : sc x ≤ 2 := bound x (Or.inl rfl)
          omega
  · by_cases hay : a = y
    · subst a
      by_cases hbx : b = x
      · subst b
        exact False.elim (hscxy (by simpa [sc] using hab.symm))
      · by_cases hby : b = y
        · subst b
          rfl
        · by_cases hbz : b = z
          · subst b
            exact False.elim (hscyz (by simpa [sc] using hab))
          · have hr : sc b = s.val b + 3 := rest b hbx hby hbz
            change sc y = sc b at hab
            rw [hr] at hab
            have ha : sc y ≤ 2 := bound y (Or.inr (Or.inl rfl))
            omega
    · by_cases haz : a = z
      · subst a
        by_cases hbx : b = x
        · subst b
          exact False.elim (hscxz (by simpa [sc] using hab.symm))
        · by_cases hby : b = y
          · subst b
            exact False.elim (hscyz (by simpa [sc] using hab.symm))
          · by_cases hbz : b = z
            · subst b
              rfl
            · have hr : sc b = s.val b + 3 := rest b hbx hby hbz
              change sc z = sc b at hab
              rw [hr] at hab
              have ha : sc z ≤ 2 := bound z (Or.inr (Or.inr rfl))
              omega
      · by_cases hbx : b = x
        · subst b
          have hr : sc a = s.val a + 3 := rest a hax hay haz
          have hb : sc x ≤ 2 := bound x (Or.inl rfl)
          change sc a = sc x at hab
          rw [hr] at hab
          omega
        · by_cases hby : b = y
          · subst b
            have hr : sc a = s.val a + 3 := rest a hax hay haz
            have hb : sc y ≤ 2 := bound y (Or.inr (Or.inl rfl))
            change sc a = sc y at hab
            rw [hr] at hab
            omega
          · by_cases hbz : b = z
            · subst b
              have hr : sc a = s.val a + 3 := rest a hax hay haz
              have hb : sc z ≤ 2 := bound z (Or.inr (Or.inr rfl))
              change sc a = sc z at hab
              rw [hr] at hab
              omega
            · have hra : sc a = s.val a + 3 := rest a hax hay haz
              have hrb : sc b = s.val b + 3 := rest b hbx hby hbz
              change sc a = sc b at hab
              rw [hra, hrb] at hab
              have hval : s.val a = s.val b := by omega
              exact s.property hval

def threeTopProfile (P : Profile V A) (x y z : A)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) : Profile V A :=
  fun v => ⟨threeTopScore (P v) x y z,
    threeTopScore_injective (P v) x y z hxy hyz hxz⟩

theorem threeTop_preserves (P : Profile V A) (x y z : A)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) (v : V) :
    (ranksAbove (threeTopProfile P x y z hxy hyz hxz v) x y ↔ ranksAbove (P v) x y) ∧
    (ranksAbove (threeTopProfile P x y z hxy hyz hxz v) y z ↔ ranksAbove (P v) y z) ∧
    (ranksAbove (threeTopProfile P x y z hxy hyz hxz v) x z ↔ ranksAbove (P v) x z) := by
  have ex : (threeTopProfile P x y z hxy hyz hxz v).val x =
      (if (P v).val y < (P v).val x then 1 else 0) +
      (if (P v).val z < (P v).val x then 1 else 0) := by
    simp [threeTopProfile, threeTopScore, hxy, Ne.symm hxy, hxz, Ne.symm hxz]
  have ey : (threeTopProfile P x y z hxy hyz hxz v).val y =
      (if (P v).val x < (P v).val y then 1 else 0) +
      (if (P v).val z < (P v).val y then 1 else 0) := by
    simp [threeTopProfile, threeTopScore, hxy, Ne.symm hxy, hyz, Ne.symm hyz]
  have ez : (threeTopProfile P x y z hxy hyz hxz v).val z =
      (if (P v).val x < (P v).val z then 1 else 0) +
      (if (P v).val y < (P v).val z then 1 else 0) := by
    simp [threeTopProfile, threeTopScore, hxz, Ne.symm hxz, hyz, Ne.symm hyz]
  refine ⟨?_, ?_, ?_⟩
  · change (threeTopProfile P x y z hxy hyz hxz v).val x <
      (threeTopProfile P x y z hxy hyz hxz v).val y ↔ (P v).val x < (P v).val y
    rw [ex, ey]
    exact predCount_lt (a := (P v).val x) (b := (P v).val y) (c := (P v).val z)
      (fun he => hxy ((P v).property he))
  · change (threeTopProfile P x y z hxy hyz hxz v).val y <
      (threeTopProfile P x y z hxy hyz hxz v).val z ↔ (P v).val y < (P v).val z
    rw [ey, ez]
    have hc := predCount_lt (a := (P v).val y) (b := (P v).val z) (c := (P v).val x) (fun he => hyz ((P v).property he))
    rw [Nat.add_comm (if (P v).val z < (P v).val y then 1 else 0) (if (P v).val x < (P v).val y then 1 else 0), Nat.add_comm (if (P v).val y < (P v).val z then 1 else 0) (if (P v).val x < (P v).val z then 1 else 0)] at hc
    exact hc
  · change (threeTopProfile P x y z hxy hyz hxz v).val x <
      (threeTopProfile P x y z hxy hyz hxz v).val z ↔ (P v).val x < (P v).val z
    rw [ex, ez]
    have hc := predCount_lt (a := (P v).val x) (b := (P v).val z) (c := (P v).val y) (fun he => hxz ((P v).property he))
    rw [Nat.add_comm (if (P v).val z < (P v).val x then 1 else 0) (if (P v).val y < (P v).val x then 1 else 0)] at hc
    exact hc

theorem threeTop_val_le2 (P : Profile V A) (x y z : A)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) (v : V) (a : A)
    (ha : a = x ∨ a = y ∨ a = z) :
    (threeTopProfile P x y z hxy hyz hxz v).val a ≤ 2 := by
  rcases ha with hax | hay | haz
  · subst a
    simp [threeTopProfile, threeTopScore, hxy, hxz]
    split_ifs <;> omega
  · subst a
    simp [threeTopProfile, threeTopScore, Ne.symm hxy, hyz]
    split_ifs <;> omega
  · subst a
    simp [threeTopProfile, threeTopScore, Ne.symm hxz, Ne.symm hyz]
    split_ifs <;> omega

theorem threeTop_val_rest (P : Profile V A) (x y z : A)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) (v : V) (w : A)
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z) :
    (threeTopProfile P x y z hxy hyz hxz v).val w = (P v).val w + 3 := by
  simp [threeTopProfile, threeTopScore, hwx, hwy, hwz]

theorem threeTop_range (f : SCF V A) (hSP : StrategyProof f) (hO : Onto f)
    (P : Profile V A) (x y z : A) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    f (threeTopProfile P x y z hxy hyz hxz) = x ∨
    f (threeTopProfile P x y z hxy hyz hxz) = y ∨
    f (threeTopProfile P x y z hxy hyz hxz) = z := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hnx, hny, hnz⟩ := hcon
  let T := threeTopProfile P x y z hxy hyz hxz
  let w := f T
  have hwx : w ≠ x := hnx
  have hwy : w ≠ y := hny
  have hwz : w ≠ z := hnz
  let R2 : Profile V A := fun v => xTopBallot (T v) x
  have hfall : ∀ (v : V) (u : A), ranksAbove (T v) w u → ranksAbove (R2 v) w u := by
    intro v u hu
    have e1 : (T v).val w = (P v).val w + 3 := by
      exact threeTop_val_rest P x y z hxy hyz hxz v w hwx hwy hwz
    have e2 : (T v).val x ≤ 2 := by
      exact threeTop_val_le2 P x y z hxy hyz hxz v x (Or.inl rfl)
    have hux : u ≠ x := by
      intro he
      subst u
      change (T v).val w < (T v).val x at hu
      rw [e1] at hu
      omega
    have e3 : (R2 v).val w = (T v).val w + 1 := by
      simp [R2, xTopBallot, xTopScore, hwx]
    have e4 : (R2 v).val u = (T v).val u + 1 := by
      simp [R2, xTopBallot, xTopScore, hux]
    change (R2 v).val w < (R2 v).val u
    rw [e3, e4]
    change (T v).val w < (T v).val u at hu
    omega
  have hfw : f R2 = w := monotone f hSP T R2 w hfall rfl
  have hfx : f R2 = x := unanimous_of_sp_onto f hSP hO R2 x
    (fun v => xTopBallot_top (T v) x)
  exact hwx (hfw.symm.trans hfx)

theorem ranksAbove_not (s : Ballot A) (x y : A) (hxy : x ≠ y) :
    ranksAbove s y x ↔ ¬ ranksAbove s x y := by
  constructor
  · exact ranksAbove_asymm s y x
  · intro h
    rcases ranksAbove_trichotomy s y x (Ne.symm hxy) with hyx | hxy'
    · exact hyx
    · exact False.elim (h hxy')

theorem topTwo_symm (P : Profile V A) (x y : A) (hxy : x ≠ y) :
    topTwoProfile P x y hxy = topTwoProfile P y x (Ne.symm hxy) := by
  funext v
  apply Subtype.ext
  funext a
  by_cases h : ranksAbove (P v) x y
  · have hnyx : ¬ ranksAbove (P v) y x := fun hc => ranksAbove_asymm _ _ _ h hc
    simp [topTwoProfile, h, hnyx]
  · have hyx : ranksAbove (P v) y x := by
      rcases ranksAbove_trichotomy (P v) y x (Ne.symm hxy) with hc | hc
      · exact hc
      · exact False.elim (h hc)
    simp [topTwoProfile, h, hyx]

theorem topTwo_preserves_flip (P : Profile V A) (x y : A) (hxy : x ≠ y) (v : V) :
    ranksAbove (topTwoProfile P x y hxy v) y x ↔ ranksAbove (P v) y x := by
  rw [ranksAbove_not (topTwoProfile P x y hxy v) x y hxy,
    ranksAbove_not (P v) x y hxy]
  exact not_congr (topTwo_preserves P x y hxy v)

/-- x beats y when x ≠ y and f selects x on the top-two profile. -/
def beats (f : SCF V A) (P : Profile V A) (x y : A) : Prop :=
  ∃ hxy : x ≠ y, f (topTwoProfile P x y hxy) = x

instance beatsDecidablePred (f : SCF V A) (P : Profile V A) (x : A) :
    DecidablePred (fun z => beats f P z x) := by
  intro z
  by_cases heq : z = x
  · subst heq
    exact isFalse (fun h => by obtain ⟨hne, _⟩ := h; exact hne rfl)
  · have hzx : z ≠ x := heq
    have hiff : beats f P z x ↔ f (topTwoProfile P z x hzx) = z := by
      constructor
      · intro h
        obtain ⟨_, e⟩ := h
        exact e
      · intro e
        exact ⟨hzx, e⟩
    haveI : Decidable (f (topTwoProfile P z x hzx) = z) := inferInstance
    exact decidable_of_iff (f (topTwoProfile P z x hzx) = z) hiff.symm

theorem beats_irrefl (f : SCF V A) (P : Profile V A) (x : A) : ¬ beats f P x x := by
  intro h
  obtain ⟨hne, _⟩ := h
  exact hne rfl

theorem beats_asymm (f : SCF V A) (P : Profile V A) (x y : A)
    (h1 : beats f P x y) (h2 : beats f P y x) : False := by
  obtain ⟨hxy, e1⟩ := h1
  obtain ⟨_, e2⟩ := h2
  have hsym := topTwo_symm P x y hxy
  have e1p : f (topTwoProfile P y x (Ne.symm hxy)) = x := by
    rw [← hsym]
    exact e1
  have hxy2 : x = y := e1p.symm.trans e2
  exact hxy hxy2

theorem beats_total (f : SCF V A) (hSP : StrategyProof f) (hO : Onto f)
    (P : Profile V A) (x y : A) (hxy : x ≠ y) :
    beats f P x y ∨ beats f P y x := by
  rcases topTwo_range f hSP hO P x y hxy with e | e
  · exact Or.inl ⟨hxy, e⟩
  · have hsym := topTwo_symm P x y hxy
    exact Or.inr ⟨Ne.symm hxy, hsym ▸ e⟩

theorem pairwise_IIA (f : SCF V A) (hSP : StrategyProof f)
    (P Q : Profile V A) (x y : A) (hxy : x ≠ y)
    (hagree : ∀ v : V, (ranksAbove (P v) x y ↔ ranksAbove (Q v) x y)) :
    (beats f P x y ↔ beats f Q x y) := by
  have key : ∀ {R1 R2 : Profile V A},
      (∀ v : V, (ranksAbove (R1 v) x y ↔ ranksAbove (R2 v) x y)) →
      (f (topTwoProfile R1 x y hxy) = x → f (topTwoProfile R2 x y hxy) = x) := by
    intro R1 R2 hag hfx
    apply monotone f hSP (topTwoProfile R1 x y hxy) (topTwoProfile R2 x y hxy) x ?_ hfx
    intro v w hw
    by_cases hwx : w = x
    · subst w
      exact (ranksAbove_irrefl _ _ hw).elim
    · by_cases hwy : w = y
      · subst w
        have h1 : ranksAbove (R1 v) x y := (topTwo_preserves R1 x y hxy v).mp hw
        have h2 : ranksAbove (R2 v) x y := (hag v).mp h1
        exact (topTwo_preserves R2 x y hxy v).mpr h2
      · exact (topTwo_above_rest R2 x y hxy v v w hwx hwy).1
  constructor
  · intro h
    obtain ⟨_, e⟩ := h
    exact ⟨hxy, key hagree e⟩
  · intro h
    obtain ⟨_, e⟩ := h
    have hag2 : ∀ v : V, (ranksAbove (Q v) x y ↔ ranksAbove (P v) x y) :=
      fun v => (hagree v).symm
    exact ⟨hxy, key hag2 e⟩

theorem beats_trans (f : SCF V A) (hSP : StrategyProof f) (hO : Onto f)
    (P : Profile V A) (x y z : A) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (h1 : beats f P x y) (h2 : beats f P y z) : beats f P x z := by
  let Q : Profile V A := threeTopProfile P x y z hxy hyz hxz
  have hag_xy : ∀ v : V, (ranksAbove (P v) x y ↔ ranksAbove (Q v) x y) :=
    fun v => ((threeTop_preserves P x y z hxy hyz hxz v).1).symm
  have hag_yz : ∀ v : V, (ranksAbove (P v) y z ↔ ranksAbove (Q v) y z) :=
    fun v => ((threeTop_preserves P x y z hxy hyz hxz v).2.1).symm
  have hag_xz : ∀ v : V, (ranksAbove (P v) x z ↔ ranksAbove (Q v) x z) :=
    fun v => ((threeTop_preserves P x y z hxy hyz hxz v).2.2).symm
  have e1Q : f (topTwoProfile Q x y hxy) = x := by
    obtain ⟨_, e⟩ := (pairwise_IIA f hSP P Q x y hxy hag_xy).mp h1
    exact e
  have e2Q : f (topTwoProfile Q y z hyz) = y := by
    obtain ⟨_, e⟩ := (pairwise_IIA f hSP P Q y z hyz hag_yz).mp h2
    exact e
  have hrange := threeTop_range f hSP hO P x y z hxy hyz hxz
  rcases hrange with hQx | hQy | hQz
  · have hfall : ∀ (v : V) (w : A), ranksAbove (Q v) x w →
        ranksAbove (topTwoProfile Q x z hxz v) x w := by
      intro v w hw
      by_cases hwx : w = x
      · subst w
        exact (ranksAbove_irrefl _ _ hw).elim
      · by_cases hwz : w = z
        · subst w
          exact (topTwo_preserves Q x z hxz v).mpr hw
        · exact (topTwo_above_rest Q x z hxz v v w hwx hwz).1
    have hR : f (topTwoProfile Q x z hxz) = x := monotone f hSP Q _ x hfall hQx
    have hag2 : ∀ v : V, (ranksAbove (Q v) x z ↔ ranksAbove (P v) x z) :=
      fun v => (hag_xz v).symm
    obtain ⟨_, e⟩ := (pairwise_IIA f hSP Q P x z hxz hag2).mp ⟨hxz, hR⟩
    exact ⟨hxz, e⟩
  · exfalso
    have hfall : ∀ (v : V) (w : A), ranksAbove (Q v) y w →
        ranksAbove (topTwoProfile Q x y hxy v) y w := by
      intro v w hw
      by_cases hwy : w = y
      · subst w
        exact (ranksAbove_irrefl _ _ hw).elim
      · by_cases hwx : w = x
        · subst w
          have g1 : ¬ ranksAbove (Q v) x y :=
            fun h => ranksAbove_asymm (Q v) y x hw h
          have g2 : ¬ ranksAbove (topTwoProfile Q x y hxy v) x y := by
            intro h
            exact g1 ((topTwo_preserves Q x y hxy v).mp h)
          rcases ranksAbove_trichotomy (topTwoProfile Q x y hxy v) x y hxy with h | h
          · exact absurd h g2
          · exact h
        · exact (topTwo_above_rest Q x y hxy v v w hwx hwy).2
    have hR : f (topTwoProfile Q x y hxy) = y := monotone f hSP Q _ y hfall hQy
    rw [e1Q] at hR
    exact hxy hR
  · exfalso
    have hfall : ∀ (v : V) (w : A), ranksAbove (Q v) z w →
        ranksAbove (topTwoProfile Q y z hyz v) z w := by
      intro v w hw
      by_cases hwz : w = z
      · subst w
        exact (ranksAbove_irrefl _ _ hw).elim
      · by_cases hwy : w = y
        · subst w
          have g1 : ¬ ranksAbove (Q v) y z :=
            fun h => ranksAbove_asymm (Q v) z y hw h
          have g2 : ¬ ranksAbove (topTwoProfile Q y z hyz v) y z := by
            intro h
            exact g1 ((topTwo_preserves Q y z hyz v).mp h)
          rcases ranksAbove_trichotomy (topTwoProfile Q y z hyz v) y z hyz with h | h
          · exact absurd h g2
          · exact h
        · exact (topTwo_above_rest Q y z hyz v v w hwy hwz).2
    have hR : f (topTwoProfile Q y z hyz) = z := monotone f hSP Q _ z hfall hQz
    rw [e2Q] at hR
    exact hyz hR

/-- Number of predecessors of x under beats. -/
def copelandScore (f : SCF V A) (P : Profile V A) (x : A) : ℕ :=
  (Finset.univ.filter (fun z => beats f P z x)).card

theorem copeland_lt_of_beats (f : SCF V A) (hSP : StrategyProof f) (hO : Onto f)
    (P : Profile V A) (x y : A) (h : beats f P x y) :
    copelandScore f P x < copelandScore f P y := by
  have hxy : x ≠ y := by
    intro heq
    subst y
    exact beats_irrefl f P x h
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    by_cases hzx : z = x
    · subst z
      exact h
    · by_cases hzy : z = y
      · subst z
        exact False.elim (beats_asymm f P x y h hz)
      · rcases beats_total f hSP hO P z y hzy with h1 | h1
        · exact h1
        · have htr := beats_trans f hSP hO P y z x (Ne.symm hzy) hzx
            (Ne.symm hxy) h1 hz
          exact False.elim (beats_asymm f P x y h htr)
  · intro heq
    have hxR : x ∈ Finset.univ.filter (fun z => beats f P z y) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h
    have hxL : x ∉ Finset.univ.filter (fun z => beats f P z x) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact beats_irrefl f P x
    rw [← heq] at hxR
    exact hxL hxR

theorem copelandScore_injective (f : SCF V A) (hSP : StrategyProof f) (hO : Onto f)
    (P : Profile V A) : Function.Injective (copelandScore f P) := by
  intro x y hsc
  by_contra hne
  have hxy : x ≠ y := hne
  rcases beats_total f hSP hO P x y hxy with h | h
  · have hlt := copeland_lt_of_beats f hSP hO P x y h
    omega
  · have hlt := copeland_lt_of_beats f hSP hO P y x h
    omega

def swfOfSCF (f : SCF V A) (hSP : StrategyProof f) (hO : Onto f) : Arrow.SWF V A :=
  fun P => ⟨copelandScore f P, copelandScore_injective f hSP hO P⟩

theorem swfOfSCF_spec (f : SCF V A) (hSP : StrategyProof f) (hO : Onto f)
    (P : Profile V A) (x y : A) (hxy : x ≠ y) :
    ranksAbove (swfOfSCF f hSP hO P) x y ↔ beats f P x y := by
  have hscore : ∀ a b : A, a ≠ b →
      (beats f P a b ↔ copelandScore f P a < copelandScore f P b) := by
    intro a b hab
    constructor
    · exact copeland_lt_of_beats f hSP hO P a b
    · intro hlt
      by_contra hnot
      rcases beats_total f hSP hO P a b hab with hab' | hba
      · exact False.elim (hnot hab')
      · have hrev := copeland_lt_of_beats f hSP hO P b a hba
        omega
  have e : (swfOfSCF f hSP hO P).val = copelandScore f P := rfl
  change (swfOfSCF f hSP hO P).val x < (swfOfSCF f hSP hO P).val y ↔ beats f P x y
  rw [e]
  exact (hscore x y hxy).symm

end GibbardSatterthwaite
