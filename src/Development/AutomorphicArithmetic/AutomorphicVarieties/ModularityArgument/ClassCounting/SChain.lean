module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps
import Development.EtaleCohomology.CyclotomicDiscriminants.FinSRel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK

namespace UpperTheory.V.ZK.SimplicialChains

variable (A : Type) [CommRing A]

private theorem bd_triv (G : Type) [Group G] [Subsingleton G] (m : ℕ) (a : A) :
    bd A G m (Finsupp.single 1 a) =
      Finsupp.single 1 ((1 + ∑ j ∈ Finset.range (m + 1), (-1 : A) ^ (j + 1)) * a) := by
  rw [_root_.LateralTheory.Q.SChainPf.bd_single]
  ext x
  simp [Finsupp.single_apply, eq_iff_true_of_subsingleton,
    Fin.sum_univ_eq_sum_range (fun j => (-1 : A) ^ (j + 1) * a), add_mul, Finset.sum_mul]

private theorem coef (m : ℕ) : (1 + ∑ j ∈ Finset.range (m + 1), (-1 : A) ^ (j + 1)) +
    (1 + ∑ j ∈ Finset.range (m + 1 + 1), (-1 : A) ^ (j + 1)) = 1 := by
  induction m with
  | zero => norm_num [Finset.sum_range_succ]
  | succ n ih =>
    rw [Finset.sum_range_succ _ (n + 1 + 1), Finset.sum_range_succ _ (n + 1)]
    rw [Finset.sum_range_succ _ (n + 1)] at ih
    linear_combination ih

private theorem triv (G : Type) [Group G] [Subsingleton G] (m : ℕ) (z : Ch A G (m + 1)) (hz : Cyc z) : Bd z := by
  have hz1 : z = Finsupp.single 1 (z 1) := by
    ext x
    obtain rfl : x = 1 := Subsingleton.elim _ _
    simp
  have h0 : (1 + ∑ j ∈ Finset.range (m + 1), (-1 : A) ^ (j + 1)) * z 1 = 0 := by
    have h := hz
    unfold Cyc at h
    rw [hz1, bd_triv] at h
    simpa using congrArg (fun w => w 1) h
  show z ∈ (bd A G (m + 1)).range
  refine LinearMap.mem_range.mpr ⟨Finsupp.single 1 (z 1), ?_⟩
  rw [bd_triv]
  conv_rhs => rw [hz1]
  congr 1
  linear_combination (z 1) * coef A m - h0

end UpperTheory.V.ZK.SimplicialChains

open UpperTheory.V.ZK.SimplicialChains in
theorem UpperTheory.V.ZK.sChain :
    UpperTheory.V.ZK.SChain := by
  intro A _
  refine ⟨fun _ _ => _root_.LateralTheory.Q.SChainPf.bd_bd (A := A),
    fun _ _ _ _ => _root_.LateralTheory.Q.SChainPf.bd_cm (A := A),
    fun _ _ _ _ _ _ f g m z => _root_.LateralTheory.Q.SChainPf.cm_comp f g m z,
    fun _ _ _ _ => _root_.LateralTheory.Q.SChainPf.cm_prism (A := A), triv A⟩
