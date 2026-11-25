module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeZeroOfSmall
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSquareIntegrable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealDirectionThetaNonzero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.ThetaPairingLaws

theorem ipO_self {D : D7} {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (f : Mx D m n → ℂ) :
    ipO μ 𝓕 f f = (nrm2 μ 𝓕 f : ℂ) := by
  unfold ipO nrm2
  rw [← integral_complex_ofReal]
  congr 1
  funext w
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem ipO_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsStdChar D ψ (-1) → IsCovolOne (ratL T S) μ 𝓕 → ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IntegrableOn (fun w => f w * (starRingEnd ℂ) (g w)) 𝓕 μ ∧ ipO μ 𝓕 g f = (starRingEnd ℂ) (ipO μ 𝓕 f g) ∧ (∀ c : ℂ, ipO μ 𝓕 (c • f) g = c * ipO μ 𝓕 f g ∧ ipO μ 𝓕 f (c • g) = (starRingEnd ℂ) c * ipO μ 𝓕 f g) ∧ (∀ f', IsThetaFunO ψ S T f' → ipO μ 𝓕 (f + f') g = ipO μ 𝓕 f g + ipO μ 𝓕 f' g ∧ ipO μ 𝓕 g (f + f') = ipO μ 𝓕 g f + ipO μ 𝓕 g f') ∧ ipO μ 𝓕 f f = (nrm2 μ 𝓕 f : ℂ) ∧ (nrm2 μ 𝓕 f = 0 → f = 0) ∧ (∀ w, ipO μ 𝓕 (heisO ψ S T w f) (heisO ψ S T w g) = ipO μ 𝓕 f g ∧ ipO μ 𝓕 (heisO ψ S T w f) g = ipO μ 𝓕 f (heisO ψ S T (-w) g)) ∧ ∀ μ' 𝓕', IsCovolOne (ratL T S) μ' 𝓕' → ipO μ' 𝓕' f g = ipO μ 𝓕 f g := by
  intro D ψ S T μ 𝓕 hψ hμ f g hf hg
  have hμ₀ := hμ
  unfold IsCovolOne at hμ₀
  obtain ⟨hHaar, hFD, -⟩ := hμ₀
  obtain ⟨-, hL2⟩ := GlobalTheory.ThetaSquare.theta_square_integrable D S T
  obtain ⟨-, hHeis, -⟩ := hL2 ψ hψ
  obtain ⟨-, hInvol, hPres, -, -⟩ := hHeis
  obtain ⟨-, -, ⟨-, hHL⟩, -⟩ := (GlobalTheory.ThetaAllChar.thetaFacts D).std hψ S T
  refine ⟨GlobalTheory.Size.integrableOn_mul_conj hψ hHaar hFD hf hg,
    (GlobalTheory.Size.ipO_conj μ 𝓕 f g).symm,
    fun c => ⟨GlobalTheory.Size.ipO_smul_left μ 𝓕 c f g,
      GlobalTheory.Size.ipO_smul_right μ 𝓕 c f g⟩,
    fun f' hf' => ⟨GlobalTheory.Size.ipO_add_left hψ hHaar hFD hf hf' hg,
      GlobalTheory.Size.ipO_add_right hψ hHaar hFD hg hf hf'⟩,
    ipO_self μ 𝓕 f,
    fun h0 => (GlobalTheory.Size.ipO_self_eq_zero_iff hψ hHaar hFD hf).1
      (by rw [GlobalTheory.Size.ipO_self, h0, Complex.ofReal_zero]),
    fun w => ⟨GlobalTheory.Size.ipO_heisO hψ hHaar hFD hf hg w, ?_⟩, ?_⟩
  · have hg' : IsThetaFunO ψ S T (heisO ψ S T (-w) g) := hPres (-w) g hg
    have e := hInvol (-w) g
    rw [neg_neg] at e
    calc ipO μ 𝓕 (heisO ψ S T w f) g
        = ipO μ 𝓕 (heisO ψ S T w f) (heisO ψ S T w (heisO ψ S T (-w) g)) := by rw [e]
      _ = ipO μ 𝓕 f (heisO ψ S T (-w) g) := GlobalTheory.Size.ipO_heisO hψ hHaar hFD hf hg' w
  · intro μ' 𝓕' h'
    have a := (hHL μ' μ 𝓕' 𝓕 h' hμ f g hf hg).2.2
    have b := (hHL μ μ 𝓕 𝓕 hμ hμ f g hf hg).2.2
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.RealDirectionThetaNonzero.heisO_apply_zero] at a b
    unfold ipO
    rw [a, b]

end GlobalTheory.ThetaPairingLaws
