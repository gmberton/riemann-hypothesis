module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.AdaptedMove

private theorem lamX_eq_of_snd_eq (I : AutInst) {p q : I.GA} (h : p.2 = q.2) : lamX I p = lamX I q := by
  unfold lamX
  rw [h]

theorem lamX_move (I : AutInst) (x x' : I.Gf) (h : ∃ γ ∈ I.GFset, ∃ k ∈ I.Kset, γ.2 * x = x' * k) :
    ∃ g : GL (Fin I.n) I.E, g ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧
      ∀ y, (g : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y ∈ lamX I (1, x') ↔ y ∈ lamX I (1, x) := by
  obtain ⟨γ, hγ, k, hk, hx⟩ := h
  obtain ⟨g, hgU, -, hgf⟩ := hγ
  refine ⟨g, hgU, fun y => ?_⟩
  have h1 : lamX I (γ * (1, x)) = lamX I (1, x') := by
    have e1 : lamX I (γ * (1, x)) = lamX I ((1, x') * (1, k)) :=
      lamX_eq_of_snd_eq I (by simp [hx])
    rw [e1]
    exact (GlobalTheory.PointEquivariance.lamX_mul_eq_iff I (1, x') (1, k)).1 hk
  have h2 := GlobalTheory.PointEquivariance.lamX_rat I (1, x) γ g hgf
  rw [h1, GlobalTheory.PointEquivariance.ratIso_apply] at h2
  rw [h2, Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, hzy⟩
    have hzy' : (g : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ z = (g : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y := by
      simpa using hzy
    rwa [← Matrix.mulVec_injective_of_isUnit g.isUnit hzy']
  · intro hy
    exact ⟨y, hy, by simp⟩

theorem isLattice_move {E : Type} [Field E] [NumberField E] {m : ℕ} (Λ Λ' : Submodule (𝓞 E) (Fin m → E))
    (γ : GL (Fin m) E) (h : ∀ y, (γ : Matrix (Fin m) (Fin m) E) *ᵥ y ∈ Λ' ↔ y ∈ Λ)
    (hΛ : Submodule.IsFullLattice E Λ) : Submodule.IsFullLattice E Λ' := by
  have hmap : Λ' = Λ.map ((Matrix.toLin' (γ : Matrix (Fin m) (Fin m) E)).restrictScalars (𝓞 E)) := by
    ext z
    simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.toLin'_apply]
    constructor
    · intro hz
      refine ⟨((γ⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ z, (h _).1 ?_, ?_⟩
      · simpa [Matrix.mulVec_mulVec] using hz
      · simp [Matrix.mulVec_mulVec]
    · rintro ⟨y, hy, rfl⟩
      exact (h y).2 hy
  have hspan : Submodule.span E (Λ : Set (Fin m → E)) ≤
      (Submodule.span E (Λ' : Set (Fin m → E))).comap
        (Matrix.toLin' (γ : Matrix (Fin m) (Fin m) E)) := by
    apply Submodule.span_le.mpr
    intro y hy
    exact Submodule.subset_span ((h y).2 hy)
  rw [hΛ.span_eq_top] at hspan
  refine { toIsLattice := ?_, span_eq_top := ?_ }
  · rw [hmap]
    exact Submodule.IsLattice.of_fg E (hΛ.fg.map _)
  · apply top_unique
    intro z _
    have hz := hspan (show ((γ⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ z ∈ ⊤ from trivial)
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec] using hz

theorem gram_mul {E : Type} [CommRing E] [StarRing E] {n p q : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (A : Matrix (Fin n) (Fin p) E) (B : Matrix (Fin n) (Fin q) E) (P : Matrix (Fin p) (Fin p) E)
    (Q : Matrix (Fin q) (Fin q) E) : (A * P)ᴴ * J * (B * Q) = Pᴴ * (Aᴴ * J * B) * Q := by
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem adapted_move : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ (Λ' : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀' : I₀.Gf), (∀ i, ∃ γ : GL (Fin (j i)) I.E, ∀ y, (γ : Matrix (Fin (j i)) (Fin (j i)) I.E) *ᵥ y ∈ Λ' i ↔ y ∈ Λ i) → (∃ γ ∈ I₀.GFset, ∃ k ∈ I₀.Kset, γ.2 * x₀ = x₀' * k) → ∃ U U' U₀, IsAdapted I I₀ e xf j S Λ' x₀' U U' U₀ := by
  intro I I₀ e xf a j S Λ x₀ T T' T₀ _ hA Λ' x₀' hΛ hx
  obtain ⟨he, hn, hlat, hiso, hdual, h0, hlam, hS⟩ := hA
  choose γ hγ using hΛ
  obtain ⟨g₀, hg₀, hg₀m⟩ := lamX_move I₀ x₀ x₀' hx
  have hinv : Formalism.UG.cT (starRingEnd I₀.E) ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val) * I₀.J *
      (g₀⁻¹ : GL (Fin I₀.n) I₀.E).val = I₀.J := (Formalism.UG.UJ _ _).inv_mem hg₀
  have hcT : Formalism.UG.cT (starRingEnd I₀.E) ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val) =
      ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val)ᴴ := by
    ext r s
    simp only [Formalism.UG.cT, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply,
      starRingEnd_apply]
  rw [hcT] at hinv
  have hc : ∀ i, ((γ i).val)ᴴ * (((γ i)⁻¹).val)ᴴ = 1 := by
    intro i
    rw [← Matrix.conjTranspose_mul, Units.inv_mul, Matrix.conjTranspose_one]
  have hG1 : ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val).map e * (g₀.val).map e = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero e) (map_one e)]
  refine ⟨fun i => T i * ((γ i)⁻¹).val, fun i => T' i * ((γ i).val)ᴴ,
    T₀ * ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val).map e, he, hn,
    fun i => isLattice_move (Λ i) (Λ' i) (γ i) (hγ i) (hlat i), ?_, ?_, ?_, ?_, ?_⟩
  · intro i k
    obtain ⟨h1, h2, h3⟩ := hiso i k
    refine ⟨?_, ?_, fun hik => ?_⟩
    · rw [gram_mul, h1, Matrix.mul_zero, Matrix.zero_mul]
    · rw [gram_mul, h2, Matrix.mul_zero, Matrix.zero_mul]
    · rw [gram_mul, h3 hik, Matrix.mul_zero, Matrix.zero_mul]
  · intro i
    obtain ⟨h1, h2, h3⟩ := hdual i
    refine ⟨?_, ?_, ?_⟩
    · rw [gram_mul, h1, Matrix.mul_one, ← Matrix.conjTranspose_mul, Units.mul_inv,
        Matrix.conjTranspose_one]
    · rw [gram_mul, h2, Matrix.mul_zero, Matrix.zero_mul]
    · rw [gram_mul, h3, Matrix.mul_zero, Matrix.zero_mul]
  · rw [gram_mul, h0, ← Matrix.conjTranspose_map e he, ← Matrix.map_mul, ← Matrix.map_mul, hinv]
  · intro z
    rw [hlam z]
    constructor
    · rintro ⟨u, u', y, hu, hu', hy, rfl⟩
      refine ⟨fun i => (γ i).val *ᵥ u i, fun i => (((γ i)⁻¹).val)ᴴ *ᵥ u' i, g₀.val *ᵥ y,
        fun i => (hγ i _).2 (hu i), fun i t ht => ?_, (hg₀m y).2 hy, ?_⟩
      · have ht' : ((γ i)⁻¹).val *ᵥ t ∈ Λ i := (hγ i _).1 (by simpa [Matrix.mulVec_mulVec] using ht)
        rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
        exact hu' i _ ht'
      · simp_rw [← RingEquiv.coe_toRingHom e, RingHom.map_mulVec, RingEquiv.coe_toRingHom e]
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.inv_mul, hc, hG1, Matrix.mul_one,
          Function.comp_def]
    · rintro ⟨w, w', y', hw, hw', hy', rfl⟩
      refine ⟨fun i => ((γ i)⁻¹).val *ᵥ w i, fun i => ((γ i).val)ᴴ *ᵥ w' i,
        (g₀⁻¹ : GL (Fin I₀.n) I₀.E).val *ᵥ y', fun i => (hγ i _).1 ?_, fun i t ht => ?_,
        (hg₀m _).1 ?_, ?_⟩
      · simpa [Matrix.mulVec_mulVec] using hw i
      · rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
        exact hw' i _ ((hγ i t).2 ht)
      · simpa [Matrix.mulVec_mulVec] using hy'
      · simp_rw [← RingEquiv.coe_toRingHom e, RingHom.map_mulVec, RingEquiv.coe_toRingHom e]
        simp only [Matrix.mulVec_mulVec, Function.comp_def]
  · intro k z
    rw [hS k z]
    constructor
    · rintro ⟨u, hu, hz, rfl⟩
      refine ⟨fun i => (γ i).val *ᵥ u i, fun i => (hγ i _).2 (hu i), fun i hi => ?_, ?_⟩
      · simp [hz i hi]
      · simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    · rintro ⟨w, hw, hz, rfl⟩
      refine ⟨fun i => ((γ i)⁻¹).val *ᵥ w i, fun i => (hγ i _).1 ?_, fun i hi => ?_, ?_⟩
      · simpa [Matrix.mulVec_mulVec] using hw i
      · simp [hz i hi]
      · simp only [Matrix.mulVec_mulVec]

end GlobalTheory.AdaptedMove
