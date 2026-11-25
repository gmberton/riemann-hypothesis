module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.StandardHermitianSpace
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVectorFockVacuum
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOperatorFixThetaDatumAwaySplitPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeForMatchedFrames

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FinZeta.VacOff

variable {D : D7}

theorem placeIdem_smul_off {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {v w : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D w ε) (hwv : w ≠ v) {u : WO S T}
    (hu : u ∈ latO S T LS LT fun x => x = v) : algebraMap (AF D.host.F) (AE D) ε • u = 0 := by
  exact GlobalTheory.SmallKerInv.placeIdem_smul_offP hε hwv hu

theorem idemSum_mul_off {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D} {Pset : Finset (Pl D.host.E)} (he : IsIdemSum e Pset)
    (hv : ∀ PP ∈ Pset, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) {u : WO S T} (hu : u ∈ latO S T LS LT fun x => x = v) (a b) :
    e * u a b = 0 ∧ cA D e * u a b = 0 := by
  exact GlobalTheory.SmallKerInv.idemSum_mul_offP he hv hu a b

end GlobalTheory.FinZeta.VacOff


open GlobalTheory.FinZeta.VacOff in
theorem GlobalTheory.FinZeta.levVec_vacFin : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ ∀ v ∉ finS R t, VacFin R.ψ (Vc D i) (Wc D i) v f := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R F i t σ s P cμ cη m ω BW f₀ f c io h
  obtain ⟨hC, -, -, -, -, -, -, hlv, hpt, -, -⟩ := h
  have hθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) f := by
    have := hpt 1
    unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt pureTensorO at this
    rwa [GlobalTheory.AdTh.VecFock.pureTensorL_one] at this
  refine ⟨hθ, fun v hv => ⟨hθ, ?_⟩⟩
  obtain ⟨hf₀, e, he, hth⟩ := hlv
  have hV : (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) = (frameLat (Vc D i) : Set _) := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.StandardHermitianSpace.baseLat_eq hC.lev i, GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]
  have hW : (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) = (frameLat (Wc D i) : Set _) := by
    rw [← GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]
    obtain ⟨c, -, -, -, h1, h2⟩ := hC.lev.βW i
    ext x
    constructor
    · intro hx
      simpa using h2 x hx
    · intro hx
      simpa using h1 x hx
  have hlat := hf₀.2.lat
  have hle : latO (Vc D i) (Wc D i) (frameLat (Vc D i) : Set _) (frameLat (Wc D i) : Set _) (fun u => u = v) ≤
      latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True := by
    rw [hV, hW]
    exact GlobalTheory.PlaceTensor.latO_mono fun _ _ => trivial
  have hoff : ∀ PP ∈ (R.datWp i P).Pg ∪ R.Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v := fun PP hPP h0 =>
    hv (Finset.mem_image.2 ⟨PP, hPP, h0⟩)
  have hz : ∀ u ∈ latO (Vc D i) (Wc D i) (frameLat (Vc D i) : Set _) (frameLat (Wc D i) : Set _) (fun u => u = v),
      ∀ a b, cA D e * u a b = 0 ∧ cA D (cA D e) * u a b = 0 := fun u hu a b => by
    obtain ⟨h1, h2⟩ := idemSum_mul_off he hoff hu a b
    rw [GlobalTheory.DualPairCheck.cA_cA]
    exact ⟨h2, h1⟩
  refine ⟨fun u hu => ?_, fun e' he' u hu hh => ?_⟩
  · exact GlobalTheory.Hk3.heisO_fix_thetaAt_off R.ψ _ _ _ _ _ _ _ _ hth (2 • u)
      (hz _ (AddSubgroup.nsmul_mem _ hu 2)) (hlat.1 u (hle hu))
  · exact GlobalTheory.Hk3.heisO_fix_thetaAt_off R.ψ _ _ _ _ _ _ _ _ hth u (hz u hu) (hlat.2 e' he' u (hle hu) hh)
