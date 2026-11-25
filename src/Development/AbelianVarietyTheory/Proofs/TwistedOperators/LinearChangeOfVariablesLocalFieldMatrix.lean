module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Kronecker

namespace GlobalTheory.SplitWeil

theorem map_curry_symm_pi_pi {X a b : Type} [MeasurableSpace X] [Fintype a] [Fintype b] (ν : Measure X)
    [SigmaFinite ν] :
    Measure.map (MeasurableEquiv.curry b a X).symm (Measure.pi fun _ : b => Measure.pi fun _ : a => ν) =
      Measure.pi fun _ : b × a => ν := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (MeasurableEquiv.curry b a X).symm.measurable (MeasurableSet.univ_pi hs)]
  have hpre : (MeasurableEquiv.curry b a X).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i : b => Set.univ.pi fun j : a => s (i, j) := by
    ext x
    simp [MeasurableEquiv.coe_curry_symm, Prod.forall]
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  (ν : Measure k) [ν.IsAddHaarMeasure]

omit [MeasurableSpace k] [BorelSpace k] in
theorem nabs_pos' (x : kˣ) : 0 < nabs k x := by
  show (0 : ℝ) < ((distribHaarChar k x : NNReal) : ℝ)
  exact NNReal.coe_pos.mpr distribHaarChar_pos

private lemma integral_comp_mulVec_eq_nabs_inv_smul {M : Matrix a a k} (hM : M.det ≠ 0) (u : kˣ) (hu : (u : k) = M.det)
    (f : (a → k) → ℂ) :
    ∫ x, f (M.mulVec x) ∂(Measure.pi fun _ : a => ν) =
      ((nabs k u)⁻¹ : ℝ) • ∫ x, f x ∂(Measure.pi fun _ : a => ν) := by
  have : SecondCountableTopology k := secondCountable k
  have hm : ∀ A : Matrix a a k, Measurable A.mulVec := fun A =>
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have hdet : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  let e : (a → k) ≃ᵐ (a → k) :=
    { toFun := M.mulVec, invFun := M⁻¹.mulVec
      left_inv := fun x => by simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet]
      right_inv := fun x => by simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet]
      measurable_toFun := hm M, measurable_invFun := hm M⁻¹ }
  have h1 : ∫ x, f (M.mulVec x) ∂(Measure.pi fun _ : a => ν) =
      ∫ y, f y ∂(Measure.map e (Measure.pi fun _ : a => ν)) := (e.measurableEmbedding.integral_map f).symm
  have h2 : (e : (a → k) → (a → k)) = M.mulVec := rfl
  have h0 : ((nabs k u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (nabs_pos' u).ne'
  rw [Complex.real_smul, Complex.ofReal_inv]
  apply mul_left_cancel₀ h0
  rw [← mul_assoc, mul_inv_cancel₀ h0, one_mul, h1, h2]
  conv_rhs => rw [← GlobalTheory.WeilM.smul_map_mulVec_pi ν M u hu, integral_smul_measure]
  simp [nabs]

theorem integral_comp_mulVec_eq_smul (g : GL a k) (f : (a → k) → ℂ) :
    ∫ x, f (g.val.mulVec x) ∂(Measure.pi fun _ => ν) =
      ((nabs k (Matrix.GeneralLinearGroup.det g))⁻¹ : ℝ) • ∫ x, f x ∂(Measure.pi fun _ => ν) := by
  exact integral_comp_mulVec_eq_nabs_inv_smul ν (Matrix.GeneralLinearGroup.det g).ne_zero _ rfl f

omit [BorelSpace k] [DecidableEq a] [DecidableEq b] in
theorem integral_volM_eq_pi (Φ : Matrix b a k → ℂ) :
    ∫ x, Φ x ∂(volM ν b a) = ∫ y, Φ (Matrix.of (Function.curry y)) ∂(Measure.pi fun _ : b × a => ν) := by
  have : SecondCountableTopology k := secondCountable k
  rw [← map_curry_symm_pi_pi ν, (MeasurableEquiv.curry b a k).symm.measurableEmbedding.integral_map]
  rfl

private lemma mul_of_curry_mul_eq_of_curry_kronecker_mulVec (g : GL a k) (h : GL b k) (y : b × a → k) :
    h.val * Matrix.of (Function.curry y) * g.val =
      Matrix.of (Function.curry ((h.val ⊗ₖ g.valᵀ).mulVec y)) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, Function.curry_apply, Matrix.mulVec, dotProduct,
    Matrix.kroneckerMap_apply, Matrix.transpose_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  ring

theorem integral_comp_mul_mul_volM (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ) :
    ∫ x, Φ (h.val * x * g.val) ∂(volM ν b a) =
      (nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card a : ℝ)) *
        nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card b : ℝ))) • ∫ x, Φ x ∂(volM ν b a) := by
  have hK : (h.val ⊗ₖ g.valᵀ).det ≠ 0 := by
    rw [Matrix.det_kronecker, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ (Matrix.GeneralLinearGroup.det h).ne_zero)
      (pow_ne_zero _ (Matrix.GeneralLinearGroup.det g).ne_zero)
  set u : kˣ := Matrix.GeneralLinearGroup.det h ^ Fintype.card a *
    Matrix.GeneralLinearGroup.det g ^ Fintype.card b with hu_def
  have hu : (u : k) = (h.val ⊗ₖ g.valᵀ).det := by
    rw [Matrix.det_kronecker, Matrix.det_transpose, hu_def, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val]
    rfl
  rw [integral_volM_eq_pi ν (fun x => Φ (h.val * x * g.val)), integral_volM_eq_pi ν Φ]
  simp only [mul_of_curry_mul_eq_of_curry_kronecker_mulVec g h]
  rw [integral_comp_mulVec_eq_nabs_inv_smul ν hK u hu (fun y => Φ (Matrix.of (Function.curry y)))]
  congr 1
  have hn : nabs k u = nabs k (Matrix.GeneralLinearGroup.det h) ^ Fintype.card a *
      nabs k (Matrix.GeneralLinearGroup.det g) ^ Fintype.card b := by
    simp only [nabs, hu_def, map_mul, map_pow, NNReal.coe_mul, NNReal.coe_pow]
  rw [hn, mul_inv, Real.rpow_neg (nabs_pos' _).le, Real.rpow_neg (nabs_pos' _).le, Real.rpow_natCast,
    Real.rpow_natCast]

theorem linear_change_of_variables : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (ν : Measure k) [ν.IsAddHaarMeasure], (∀ (g : GL a k) (f : (a → k) → ℂ), ∫ x, f (g.val.mulVec x) ∂(Measure.pi fun _ => ν) = ((nabs k (Matrix.GeneralLinearGroup.det g))⁻¹ : ℝ) • ∫ x, f x ∂(Measure.pi fun _ => ν)) ∧ ∀ (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ), ∫ x, Φ (h.val * x * g.val) ∂(volM ν b a) = (nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card a : ℝ)) * nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card b : ℝ))) • ∫ x, Φ x ∂(volM ν b a) := by
  intro k _ _ _ _ _ _ a b _ _ _ _ ν _
  exact ⟨fun g f => integral_comp_mulVec_eq_smul ν g f, fun g h Φ => integral_comp_mul_mul_volM ν g h Φ⟩

end GlobalTheory.SplitWeil
