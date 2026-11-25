module

public import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import
  Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterBlockDiagonal
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

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

noncomputable section
namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem const_family (n : ℕ) (χ : kˣ →* ℂˣ) :
    grp (fun _ : Fin n => χ) = (KO k (Fin n) : Set (GL (Fin n) k)) ∧
      ∀ g ∈ KO k (Fin n), theta (fun _ : Fin n => χ) g = (detChar (Fin n) χ g : ℂ) := by
  refine ⟨?_, ?_⟩
  · ext g
    simp only [grp, Set.mem_setOf_eq, SetLike.mem_coe, div_self', and_iff_left_iff_imp]
    intro _ i j _ u _ _
    rfl
  · intro g hg
    cases n with
    | zero =>
      simp [theta, detChar_apply]
      have h0 : Matrix.GeneralLinearGroup.det g = 1 := Units.ext (by simp [Matrix.det_isEmpty])
      rw [h0, map_one, Units.val_one]
    | succ n =>
      unfold theta
      rw [Fin.prod_univ_castSucc]
      have h1 : ∀ i : Fin n, ev (χ / nxt (fun _ : Fin (n+1) => χ) i.castSucc) (minor g i.castSucc) = 1 := by
        intro i
        have : nxt (fun _ : Fin (n+1) => χ) i.castSucc = χ := by
          unfold nxt; rw [dite_eq_left (by simp)]
        rw [this, div_self']; exact BlockTheta.ev_one_char _
      have h2 : nxt (fun _ : Fin (n+1) => χ) (Fin.last n) = 1 := by
        unfold nxt; rw [dite_eq_right (by simp)]
      simp only [h1, Finset.prod_const_one, one_mul, h2, div_one, BlockTheta.minor_last]
      have hv := BlockTheta.val_det_of_mem_KO hg
      unfold ev
      rw [dite_eq_left hv, detChar_apply]
      congr 2
      ext; simp

theorem const_family_main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (χ : kˣ →* ℂˣ), grp (fun _ : Fin n => χ) = (KO k (Fin n) : Set (GL (Fin n) k)) ∧ ∀ g ∈ KO k (Fin n), theta (fun _ : Fin n => χ) g = (detChar (Fin n) χ g : ℂ) :=
  fun _ _ _ _ _ n χ => const_family n χ

end GlobalTheory.PsType
