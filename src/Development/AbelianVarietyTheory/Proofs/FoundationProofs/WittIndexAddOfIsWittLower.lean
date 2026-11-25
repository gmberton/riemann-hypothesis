module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th GlobalTheory.Cusp
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp)
open Module

namespace GlobalTheory.Cusp.WittIdx

section Lin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {V : Formalism.BasicNotions.HSpace E}

theorem mem_perp' {W : Submodule E V.V} {y : V.V} : y ∈ perp V W ↔ ∀ x ∈ W, V.hT x y = 0 := by
  simp only [perp, Submodule.mem_iInf, LinearMap.mem_ker]

theorem finrank_add_finrank_perp (A : Submodule E V.V) : finrank E A + finrank E (perp V A) = V.rank := by
  have hinj : Function.Injective V.hT :=
    LinearMap.ker_eq_bot.1 (LinearMap.separatingLeft_iff_ker_eq_bot.1 V.nondeg.1)
  let e := Submodule.equivMapOfInjective V.hT hinj A
  have hfr : finrank E (A.map V.hT) = finrank E A :=
    congrArg Cardinal.toNat (rank_eq_of_equiv_equiv (starRingEnd E) e.toAddEquiv
      (Function.Involutive.bijective (starRingEnd_self_apply (R := E)))
      (fun r m => e.map_smulₛₗ r m)).symm
  have hperp : perp V A = (A.map V.hT).dualCoannihilator := by
    ext y
    simp [mem_perp', Submodule.mem_dualCoannihilator]
  have h := Subspace.finrank_add_finrank_dualCoannihilator_eq (A.map V.hT)
  rwa [hfr, ← hperp, V.rank_eq] at h

end Lin

end GlobalTheory.Cusp.WittIdx
