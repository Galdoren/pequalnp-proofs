import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_989_aux

open Module MvPolynomial
open scoped BigOperators Matrix

def pairing {F : Type} [Field F] (a b : Fin 3 → F) : F :=
  ∑ t : Fin 3, a t * b t

theorem lineUnique {F : Type} [Field F] (a b u v : Fin 3 → F)
    (ha : a ≠ 0) (hab : ∀ c : F, b ≠ c • a)
    (hu : u ≠ 0) (huv : ∀ c : F, v ≠ c • u)
    (hau : pairing a u = 0) (hbu : pairing b u = 0)
    (hav : pairing a v = 0) (hbv : pairing b v = 0) : False := by
  let w := crossProduct a b
  have hw : w ≠ 0 := crossProduct_ne_zero_iff_linearIndependent.2
    ((LinearIndependent.pair_iff' ha).2 (fun c h => hab c h.symm))
  have hv : v ≠ 0 := by
    intro h
    exact huv 0 (by simpa using h)
  have common (z : Fin 3 → F) (hz : z ≠ 0)
      (haz : pairing a z = 0) (hbz : pairing b z = 0) :
      Projectivization.mk F z hz = Projectivization.mk F w hw := by
    apply (Projectivization.mk_eq_mk_iff_crossProduct_eq_zero hz hw).2
    change crossProduct z (crossProduct a b) = 0
    change dotProduct a z = 0 at haz
    change dotProduct b z = 0 at hbz
    rw [cross_cross_eq_smul_sub_smul', dotProduct_comm z b]
    simp only [haz, hbz, zero_smul, sub_zero]
  have h := (common v hv hav hbv).trans (common u hu hau hbu).symm
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' F v u hv hu).1 h
  exact huv c hc.symm

abbrev Pairs (α : Type) [Fintype α] := ↥((Finset.univ : Finset α).powersetCard 2)

theorem pairsCard (α : Type) [Fintype α] :
    Fintype.card (Pairs α) = (Fintype.card α).choose 2 := by
  simp [Pairs, Finset.card_powersetCard]

theorem twiceChoose (b : ℕ) :
    2 * (b + 2).choose 2 = (b + 1) * (b + 2) := by
  have h := Nat.choose_mul (n := b + 2) (k := 2) (s := 1) (by decide)
  rw [Nat.choose_one_right, Nat.choose_one_right, Nat.choose_one_right,
    show b + 2 - 1 = b + 1 by omega] at h
  simpa only [mul_comm] using h

abbrev Exps (b : ℕ) := {s : Fin 3 →₀ ℕ // s.degree = b}

theorem expSum {b : ℕ} (s : Exps b) : s.val 0 + s.val 1 + s.val 2 = b := by
  simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_three] using s.property

def expPair {b : ℕ} (s : Exps b) : Pairs (Fin (b + 2)) := by
  let u : Fin (b + 2) := ⟨s.val 0, by have := expSum s; omega⟩
  let v : Fin (b + 2) := ⟨s.val 0 + s.val 1 + 1, by have := expSum s; omega⟩
  refine ⟨{u, v}, ?_⟩
  have ne : u ≠ v := by
    intro h
    have e := congrArg Fin.val h
    dsimp [u, v] at e
    omega
  simp [Finset.mem_powersetCard, ne]

theorem expPairInj (b : ℕ) : Function.Injective (@expPair b) := by
  intro x y e
  have he := congrArg Subtype.val e
  let a : Fin (b + 2) := ⟨x.val 0, by have := expSum x; omega⟩
  let c : Fin (b + 2) := ⟨x.val 0 + x.val 1 + 1, by have := expSum x; omega⟩
  let a' : Fin (b + 2) := ⟨y.val 0, by have := expSum y; omega⟩
  let c' : Fin (b + 2) := ⟨y.val 0 + y.val 1 + 1, by have := expSum y; omega⟩
  change ({a, c} : Finset (Fin (b + 2))) = {a', c'} at he
  have am : a = a' ∨ a = c' := by
    have h : a ∈ ({a', c'} : Finset (Fin (b + 2))) := by rw [← he]; simp
    simpa using h
  have cm : c = a' ∨ c = c' := by
    have h : c ∈ ({a', c'} : Finset (Fin (b + 2))) := by rw [← he]; simp
    simpa using h
  have atlt : a.val < c.val := by dsimp [a, c]; omega
  have btlt : a'.val < c'.val := by dsimp [a', c']; omega
  have dat : a.val = a'.val ∧ c.val = c'.val := by
    rcases am with h | h <;> rcases cm with h' | h' <;>
      have ha := congrArg Fin.val h <;> have hc := congrArg Fin.val h' <;> omega
  have dx := expSum x
  have dy := expSum y
  dsimp [a, c, a', c'] at dat
  have e0 : x.val 0 = y.val 0 := by omega
  have e1 : x.val 1 = y.val 1 := by omega
  have e2 : x.val 2 = y.val 2 := by omega
  apply Subtype.ext
  apply Finsupp.ext
  intro j
  fin_cases j
  · exact e0
  · exact e1
  · exact e2

theorem degreeDim (F : Type) [Field F] (b : ℕ) :
    2 * finrank F (homogeneousSubmodule (Fin 3) F b) ≤ (b + 1) * (b + 2) := by
  classical
  letI : Finite (Exps b) := Finite.of_injective expPair (expPairInj b)
  letI : Fintype (Exps b) := Fintype.ofFinite _
  have h := Fintype.card_le_of_injective expPair (expPairInj b)
  rw [pairsCard, Fintype.card_fin] at h
  have hr := twiceChoose b
  rw [homogeneousSubmodule_eq_finsupp_supported,
    (AddMonoidAlgebra.supportedEquivFinsupp (R := F) {s : Fin 3 →₀ ℕ | s.degree = b}).finrank_eq,
    Module.finrank_finsupp, Module.finrank_self, mul_one]
  change 2 * Fintype.card (Exps b) ≤ (b + 1) * (b + 2)
  exact (Nat.mul_le_mul_left 2 h).trans (le_of_eq hr)

noncomputable def linearPoly {F : Type} [Field F] (a : Fin 3 → F) :
    MvPolynomial (Fin 3) F :=
  ∑ j : Fin 3, C (a j) * X j

theorem upperBound (F : Type) [Field F] (n k b : ℕ)
    (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n))
    (g : (Fin n → Bool) → Bool)
    (hpt : ∀ p, pt p ≠ 0)
    (hprop : ∀ p p', p ≠ p' → ∀ c : F, pt p' ≠ c • pt p)
    (hl : ∀ i, l i ≠ 0)
    (hlprop : ∀ i j, i ≠ j → ∀ c : F, l j ≠ c • l i)
    (hcard : ∀ i, (y i).card ≤ b)
    (hoff : ∀ i, ∀ p ∈ y i, pairing (pt p) (l i) ≠ 0)
    (hsafe : ∀ (i : Fin k) (x : Fin n → Bool), g x = true →
      ∃ p, x p = true ∧ pairing (pt p) (l i) = 0)
    (hactive : ∀ i, ∃ p p', p ≠ p' ∧ pairing (pt p) (l i) = 0 ∧
      pairing (pt p') (l i) = 0 ∧
      g (fun v => decide (v ∈ y i ∨ v = p)) = true ∧
      g (fun v => decide (v ∈ y i ∨ v = p')) = true) :
    2 * k ≤ (b + 1) * (b + 2) := by
  classical
  have hit (i j : Fin k) (hij : i ≠ j) :
      ∃ p ∈ y i, pairing (pt p) (l j) = 0 := by
    by_contra h
    obtain ⟨p, q, hpq, pi, qi, pg, qg⟩ := hactive i
    have forced (w : Fin n) (wg : g (fun v => decide (v ∈ y i ∨ v = w)) = true) :
        pairing (pt w) (l j) = 0 := by
      obtain ⟨z, hz, hline⟩ := hsafe j _ wg
      rcases of_decide_eq_true hz with hm | eq
      · exact (h ⟨z, hm, hline⟩).elim
      · simpa only [eq] using hline
    exact lineUnique (pt p) (pt q) (l i) (l j) (hpt p) (hprop p q hpq)
      (hl i) (hlprop i j hij) pi qi (forced p pg) (forced q qg)
  have existsCoord (i : Fin k) : ∃ t : Fin 3, l i t ≠ 0 := by
    by_contra! h
    exact hl i (funext h)
  choose coord hcoord using existsCoord
  let poly (i : Fin k) : MvPolynomial (Fin 3) F :=
    X (coord i) ^ (b - (y i).card) * ∏ p ∈ y i, linearPoly (pt p)
  let H := homogeneousSubmodule (Fin 3) F b
  have hom (i : Fin k) : poly i ∈ H := by
    apply (mem_homogeneousSubmodule b _).2
    have hprod := IsHomogeneous.prod (y i) (fun p => linearPoly (pt p)) (fun _ => 1) (by
      intro p _
      exact IsHomogeneous.sum _ _ _ (fun t _ => isHomogeneous_C_mul_X _ _))
    have h := (isHomogeneous_X_pow (R := F) (coord i) (b - (y i).card)).mul hprod
    simpa [poly, Nat.sub_add_cancel (hcard i)] using h
  let Q (i : Fin k) : H := ⟨poly i, hom i⟩
  have atLine (i j : Fin k) :
      aeval (l j) (poly i) =
        l j (coord i) ^ (b - (y i).card) * ∏ p ∈ y i, pairing (pt p) (l j) := by
    simp [poly, linearPoly, pairing]
  have hself (i : Fin k) : aeval (l i) (poly i) ≠ 0 := by
    rw [atLine]
    exact mul_ne_zero (pow_ne_zero _ (hcoord i))
      (Finset.prod_ne_zero_iff.mpr (hoff i))
  have hother (i j : Fin k) (hne : i ≠ j) : aeval (l j) (poly i) = 0 := by
    obtain ⟨p, hp, hpi⟩ := hit i j hne
    rw [atLine, Finset.prod_eq_zero hp hpi, mul_zero]
  have hlin : LinearIndependent F Q := by
    rw [linearIndependent_iff']
    intro s a eq i hi
    let ev : H →ₗ[F] F := (aeval (l i)).toLinearMap.comp H.subtype
    have e := congrArg ev eq
    simp only [map_sum, map_smul, map_zero] at e
    rw [Finset.sum_eq_single i (fun j hj hji => by
      have h : ev (Q j) = 0 := hother j i hji
      rw [h, smul_zero]) (fun hn => False.elim (hn hi))] at e
    change a i * aeval (l i) (poly i) = 0 at e
    exact (mul_eq_zero.mp e).resolve_right (hself i)
  letI : Module.Finite F H := Module.Finite.iff_fg.2 (homogeneousSubmodule_fg (Fin 3) F b)
  have kl : k ≤ finrank F H := by simpa using hlin.fintype_card_le_finrank
  have hu : 2 * finrank F H ≤ (b + 1) * (b + 2) := degreeDim F b
  exact (Nat.mul_le_mul_left 2 kl).trans hu

def arcVec {F α : Type} [Field F] (t : α → F) : Option α → Fin 3 → F
  | none => ![0, 0, 1]
  | some i => ![1, t i, (t i) ^ 2]

def secantVec {F α : Type} [Field F] (t : α → F) : Option α → Option α → Fin 3 → F
  | none, none => ![1, 0, 0]
  | none, some j => ![-t j, 1, 0]
  | some i, none => ![-t i, 1, 0]
  | some i, some j => ![t i * t j, -(t i + t j), 1]

theorem arcNonzero {F α : Type} [Field F] (t : α → F) (u : Option α) : arcVec t u ≠ 0 := by
  intro h
  cases u with
  | none => simpa [arcVec] using congrFun h (2 : Fin 3)
  | some j => simpa [arcVec] using congrFun h (0 : Fin 3)

theorem secantNonzero {F α : Type} [Field F] (t : α → F) (u v : Option α) :
    secantVec t u v ≠ 0 := by
  intro h
  cases u <;> cases v
  · simpa [secantVec] using congrFun h (0 : Fin 3)
  · simpa [secantVec] using congrFun h (1 : Fin 3)
  · simpa [secantVec] using congrFun h (1 : Fin 3)
  · simpa [secantVec] using congrFun h (2 : Fin 3)

theorem eqOfArcProp {F α : Type} [Field F] {t : α → F} (ht : Function.Injective t)
    (u v : Option α) (c : F) (e : arcVec t v = c • arcVec t u) : u = v := by
  cases u with
  | none =>
    cases v with
    | none => rfl
    | some j =>
      have f := congrFun e (0 : Fin 3)
      simp [arcVec, Pi.smul_apply, smul_eq_mul] at f
  | some i =>
    cases v with
    | none =>
      have hc : 0 = c := by simpa [arcVec, Pi.smul_apply, smul_eq_mul] using congrFun e (0 : Fin 3)
      have f := congrFun e (2 : Fin 3)
      simp [arcVec, Pi.smul_apply, smul_eq_mul, ← hc] at f
    | some j =>
      have hc : 1 = c := by simpa [arcVec, Pi.smul_apply, smul_eq_mul] using congrFun e (0 : Fin 3)
      have h : t j = t i := by
        simpa [arcVec, Pi.smul_apply, smul_eq_mul, ← hc] using congrFun e (1 : Fin 3)
      exact congrArg Option.some (ht h).symm

theorem exactSecant {F α : Type} [Field F] {t : α → F} (ht : Function.Injective t)
    (u v z : Option α) (hne : u ≠ v) :
    pairing (arcVec t z) (secantVec t u v) = 0 ↔ z = u ∨ z = v := by
  cases u with
  | none =>
    cases v with
    | none => exact (hne rfl).elim
    | some j =>
      cases z with
      | none => simp [arcVec, secantVec, pairing, Fin.sum_univ_three]
      | some s =>
        have e : pairing (arcVec t (some s)) (secantVec t none (some j)) = t s - t j := by
          simp [arcVec, secantVec, pairing, Fin.sum_univ_three]
          ring
        simp [e, sub_eq_zero, ht.eq_iff]
  | some i =>
    cases v with
    | none =>
      cases z with
      | none => simp [arcVec, secantVec, pairing, Fin.sum_univ_three]
      | some s =>
        have e : pairing (arcVec t (some s)) (secantVec t (some i) none) = t s - t i := by
          simp [arcVec, secantVec, pairing, Fin.sum_univ_three]
          ring
        simp [e, sub_eq_zero, ht.eq_iff]
    | some j =>
      cases z with
      | none => simp [arcVec, secantVec, pairing, Fin.sum_univ_three]
      | some s =>
        have e : pairing (arcVec t (some s)) (secantVec t (some i) (some j)) =
            (t s - t i) * (t s - t j) := by
          simp [arcVec, secantVec, pairing, Fin.sum_univ_three]
          ring
        simp [e, mul_eq_zero, sub_eq_zero, ht.eq_iff]

theorem pairingScaleLeft {F : Type} [Field F] (a b : Fin 3 → F) (c : F) :
    pairing (c • a) b = c * pairing a b := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem pairingScaleRight {F : Type} [Field F] (a b : Fin 3 → F) (c : F) :
    pairing a (c • b) = c * pairing a b := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

set_option maxHeartbeats 1500000 in
theorem attainable (F : Type) [Field F] [Fintype F] (b : ℕ) (hb : b + 1 ≤ Fintype.card F) :
    ∃ (n k : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F)
      (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool),
      (∀ p, pt p ≠ 0) ∧
      (∀ p p', p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) ∧
      (∀ v : Fin 3 → F, v ≠ 0 → ∃ (p : Fin n) (c : F), v = c • pt p) ∧
      (∀ i, l i ≠ 0) ∧ (∀ i j, i ≠ j → ∀ c : F, l j ≠ c • l i) ∧
      (∀ i, (y i).card ≤ b) ∧
      (∀ i, ∀ p ∈ y i, pairing (pt p) (l i) ≠ 0) ∧
      (∀ x x', (∀ v, x v = true → x' v = true) → g x = true → g x' = true) ∧
      (∀ (i : Fin k) (x : Fin n → Bool), g x = true →
        ∃ p : Fin n, x p = true ∧ pairing (pt p) (l i) = 0) ∧
      (∀ i, ∃ p p', p ≠ p' ∧ pairing (pt p) (l i) = 0 ∧ pairing (pt p') (l i) = 0 ∧
        g (fun v => decide (v ∈ y i ∨ v = p)) = true ∧
        g (fun v => decide (v ∈ y i ∨ v = p')) = true) ∧
      2 * k = (b + 1) * (b + 2) := by
  classical
  let I := Option (Fin (b + 1))
  let t (i : Fin (b + 1)) : F := (Fintype.equivFin F).symm (Fin.castLE hb i)
  have ht : Function.Injective t := (Fintype.equivFin F).symm.injective.comp (Fin.castLE_injective hb)
  let P := Projectivization F (Fin 3 → F)
  letI : Fintype P := Fintype.ofFinite P
  let n := Fintype.card P
  let en : P ≃ Fin n := Fintype.equivFin P
  let pt (i : Fin n) : Fin 3 → F := (en.symm i).rep
  have hpt (i : Fin n) : pt i ≠ 0 := Projectivization.rep_ne_zero _
  have mkpt (i : Fin n) : Projectivization.mk F (pt i) (hpt i) = en.symm i :=
    Projectivization.mk_rep _
  have distinctPoints (p q : Fin n) (hne : p ≠ q) (c : F) : pt q ≠ c • pt p := by
    intro h
    have eq := (Projectivization.mk_eq_mk_iff' F (pt q) (pt p) (hpt q) (hpt p)).2 ⟨c, h.symm⟩
    rw [mkpt, mkpt] at eq
    exact hne (en.symm.injective eq.symm)
  have allPoints (v : Fin 3 → F) (hv : v ≠ 0) : ∃ (p : Fin n) (c : F), v = c • pt p := by
    let p := en (Projectivization.mk F v hv)
    have eq : Projectivization.mk F v hv = Projectivization.mk F (pt p) (hpt p) := by
      rw [mkpt]
      simp [p]
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' F v (pt p) hv (hpt p)).1 eq
    exact ⟨p, c, hc.symm⟩
  let point (j : I) := en (Projectivization.mk F (arcVec t j) (arcNonzero t j))
  have pointInj : Function.Injective point := by
    intro i j h
    have he := en.injective h
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' F _ _ (arcNonzero t i) (arcNonzero t j)).1 he
    exact eqOfArcProp ht j i c hc.symm |>.symm
  have dotArc (i : I) (v : Fin 3 → F) :
      pairing (pt (point i)) v = 0 ↔ pairing (arcVec t i) v = 0 := by
    have eq : Projectivization.mk F (pt (point i)) (hpt (point i)) =
        Projectivization.mk F (arcVec t i) (arcNonzero t i) := by
      rw [mkpt]
      simp [point]
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' F _ _ (hpt (point i)) (arcNonzero t i)).1 eq
    have hc0 : c ≠ 0 := by
      intro h
      exact hpt (point i) (by rw [← hc, h, zero_smul])
    rw [← hc, pairingScaleLeft, mul_eq_zero]
    simp [hc0]
  let k := Fintype.card (Pairs I)
  let ek : Pairs I ≃ Fin k := Fintype.equivFin _
  let pair (i : Fin k) : Finset I := (ek.symm i).val
  have pairCard (i : Fin k) : (pair i).card = 2 :=
    (Finset.mem_powersetCard.1 (ek.symm i).property).2
  have pairInj : Function.Injective pair := fun _ _ h => ek.symm.injective (Subtype.ext h)
  have ends (i : Fin k) : ∃ u v : I, u ≠ v ∧ pair i = {u, v} :=
    Finset.card_eq_two.1 (pairCard i)
  choose a z diff setEq using ends
  let l (i : Fin k) := secantVec t (a i) (z i)
  have hl (i : Fin k) : l i ≠ 0 := secantNonzero t _ _
  have inc (i : Fin k) (j : I) : pairing (pt (point j)) (l i) = 0 ↔ j ∈ pair i := by
    rw [dotArc, setEq i]
    simpa only [Finset.mem_insert, Finset.mem_singleton] using exactSecant ht (a i) (z i) j (diff i)
  have distinctLines (i j : Fin k) (hne : i ≠ j) (c : F) : l j ≠ c • l i := by
    intro eq
    have hc : c ≠ 0 := by
      intro h
      exact hl j (by rw [eq, h, zero_smul])
    apply hne
    apply pairInj
    ext r
    rw [← inc i r, ← inc j r, eq, pairingScaleRight, mul_eq_zero]
    simp [hc]
  let y (i : Fin k) : Finset (Fin n) := (Finset.univ \ pair i).image point
  have yCard (i : Fin k) : (y i).card ≤ b := by
    have e : (y i).card = b := by
      change ((Finset.univ \ pair i).image point).card = b
      rw [Finset.card_image_of_injective _ pointInj, Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_univ, pairCard]
      simp [I]
    omega
  have yOff (i : Fin k) (p : Fin n) (hp : p ∈ y i) : pairing (pt p) (l i) ≠ 0 := by
    intro e
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hp
    exact (Finset.mem_sdiff.1 hj).2 ((inc i j).1 e)
  let g (x : Fin n → Bool) : Bool := decide (∀ i : Fin k, ∃ j ∈ pair i, x (point j) = true)
  have good (x : Fin n → Bool) : g x = true ↔ ∀ i : Fin k, ∃ j ∈ pair i, x (point j) = true := by
    simp only [g, decide_eq_true_eq]
  have mono (x x' : Fin n → Bool) (h : ∀ v, x v = true → x' v = true)
      (hx : g x = true) : g x' = true := by
    apply (good x').2
    intro i
    obtain ⟨j, hj, hjx⟩ := (good x).1 hx i
    exact ⟨j, hj, h _ hjx⟩
  have safe (i : Fin k) (x : Fin n → Bool) (hx : g x = true) :
      ∃ p, x p = true ∧ pairing (pt p) (l i) = 0 := by
    obtain ⟨j, hj, hjx⟩ := (good x).1 hx i
    exact ⟨point j, hjx, (inc i j).2 hj⟩
  have aMem (j : Fin k) : a j ∈ pair j := by rw [setEq]; simp
  have zMem (j : Fin k) : z j ∈ pair j := by rw [setEq]; simp
  have activation (i : Fin k) (u v : I) (huv : pair i = {u, v}) :
      g (fun w => decide (w ∈ y i ∨ w = point u)) = true := by
    refine (good (fun w => decide (w ∈ y i ∨ w = point u))).2 ?_
    intro j
    have existsR : ∃ r ∈ pair j, r ≠ v := by
      by_cases h : a j = v
      · exact ⟨z j, zMem j, fun eq => diff j (h.trans eq.symm)⟩
      · exact ⟨a j, aMem j, h⟩
    obtain ⟨r, hr, hrv⟩ := existsR
    refine ⟨r, hr, decide_eq_true ?_⟩
    by_cases h : r ∈ pair i
    · rw [huv] at h
      have either : r = u ∨ r = v := by simpa using h
      exact Or.inr (congrArg point (either.resolve_right hrv))
    · exact Or.inl (Finset.mem_image.2 ⟨r, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, h⟩, rfl⟩)
  refine ⟨n, k, pt, l, y, g, hpt, distinctPoints, allPoints, hl, distinctLines, yCard, yOff, mono, safe, ?_, ?_⟩
  · intro i
    refine ⟨point (a i), point (z i), fun eq => diff i (pointInj eq),
      (inc i _).2 (aMem i), (inc i _).2 (zMem i), activation i _ _ (setEq i), ?_⟩
    apply activation i (z i) (a i)
    rw [Finset.pair_comm]
    exact setEq i
  · have hk : k = (b + 2).choose 2 := by
      simp [k, pairsCard, I]
    rw [hk, twiceChoose]

end PEqualNP.Outside.L_meta_989_aux

theorem PEqualNP.Outside.L_meta_989 :
  (∀ (F : Type) [Field F] (n k b : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) → (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) → (∀ i : Fin k, l i ≠ 0) → (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) → (∀ i : Fin k, (y i).card ≤ b) → (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) → (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) → (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) → 2 * k ≤ (b + 1) * (b + 2)) ∧ (∀ (F : Type) [Field F] [Fintype F] (b : ℕ), b + 1 ≤ Fintype.card F → ∃ (n k : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) ∧ (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) ∧ (∀ v : Fin 3 → F, v ≠ 0 → ∃ (p : Fin n) (c : F), v = c • pt p) ∧ (∀ i : Fin k, l i ≠ 0) ∧ (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) ∧ (∀ i : Fin k, (y i).card ≤ b) ∧ (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) ∧ (∀ x x' : Fin n → Bool, (∀ v : Fin n, x v = true → x' v = true) → g x = true → g x' = true) ∧ (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) ∧ (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) ∧ 2 * k = (b + 1) * (b + 2)) := by
  exact ⟨PEqualNP.Outside.L_meta_989_aux.upperBound, PEqualNP.Outside.L_meta_989_aux.attainable⟩
