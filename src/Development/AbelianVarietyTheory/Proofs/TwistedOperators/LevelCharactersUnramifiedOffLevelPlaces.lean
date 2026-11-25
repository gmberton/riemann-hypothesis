module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemNotMem
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterUnramifiedMu
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepSplittingCharactersTameLevelResidue

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct

namespace GlobalTheory
namespace LevelPlaces
open Formalism.L2.Col Formalism.HermitianLatticesTheory GlobalTheory.SplitOffPlaces

theorem under_eq_of_isConjPl {D : D7} {P P' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.IndefR.Lev.IsConjPl P P') :
    P.under (𝓞 D.host.F) = P'.under (𝓞 D.host.F) := by
  exact GlobalTheory.BotTripleUnr.under_eq_of_isConjPl h

theorem natCast_mem_of_isConjPl {D : D7} {P P' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.IndefR.Lev.IsConjPl P P')
    {n : ℕ} (hn : (n : 𝓞 D.host.E) ∈ P.asIdeal) : (n : 𝓞 D.host.E) ∈ P'.asIdeal := by
  exact GlobalTheory.StepLaw.natCast_mem_of_isConjPl h hn

theorem isConjPl_conjSpec {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.IndefR.Lev.IsConjPl P (conjSpec P) :=
  fun c hc => ⟨cO D.host.E c, by
    change cO D.host.E (cO D.host.E c) ∈ P.asIdeal
    rwa [cO_cO], rfl⟩

theorem not_mem_of_prime {A : Type} [CommRing A] {I : Ideal A} (hI : I ≠ ⊤) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : q ≠ p) (h : (q : A) ∈ I) : (p : A) ∉ I := by
  intro h'
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hp).2 hne)
  apply hI
  rw [Ideal.eq_top_iff_one]
  have e : (1 : A) = a * (q : A) + b * (p : A) := by
    exact_mod_cast congrArg (Int.cast : ℤ → A) hab.symm
  rw [e]
  exact add_mem (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ h')

theorem div_or_div_conj {D : D7} (Pb : Formalism.L2.Host.PiBar D.host) (k : Fin 2) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hk : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) : Pb.Div k P ∨ Pb.Div k (conjSpec P) := by
  rcases GlobalTheory.ConjOverQuad.div_or_conj_div D Pb k P hk with h | ⟨w, hw, hweq⟩
  · exact Or.inl h
  · have heq : w = conjSpec P :=
      HeightOneSpectrum.ext (hweq.trans (Formalism.L2.Col.conjIdeal_eq P.asIdeal))
    exact Or.inr (heq ▸ hw)

theorem mem_of_div {D : D7} (Pb : Formalism.L2.Host.PiBar D.host) (k : Fin 2) (P : HeightOneSpectrum (𝓞 D.host.E))
    (h : Pb.Div k P) : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
  exact GlobalTheory.StepLaw.typePrime_mem_of_div h

theorem not_mem_of_twist {D : D7} {Q : Finset (Pl D.host.E)} (hQ : Formalism.IndefR.Lev.IsTwistPlaces D.host.g Q)
    {P : Pl D.host.E} (hP : P ∈ Q) (k : Fin 2) : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  obtain ⟨q, hq, hq', hne⟩ := GlobalTheory.StepLaw.exists_prime_mem_of_isTwistPlaces hQ hP
  exact fun h =>
    GlobalTheory.StepLaw.not_two_primes_mem P (D.host.g_prime k) hq (hne k).symm h hq'

end LevelPlaces


open LevelPlaces SplitOffPlaces in
theorem levCh_unramified_places : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → ∀ t : T0, Disjoint L.Pg (L.Q t) ∧ (∀ PP ∈ L.Pg, (L.xiH t).UnrAt PP) ∧ (∀ PP ∈ L.Q t, ∀ j, (L.C.mu0 j).UnrAt PP) ∧ ∀ P : Pl D.host.E, (∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q t → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ P.under (𝓞 D.host.F)) → (L.xiH t).UnrAt P ∧ ∀ j, (L.C.mu0 j).UnrAt P := by
  intro D T0 L μ0 hL t
  have hPg : ∀ PP ∈ L.Pg, ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP h => by
    obtain ⟨k, hk⟩ := (hL.Pg PP).1 h
    exact ⟨k, mem_of_div _ k PP hk⟩
  have hQ : ∀ PP ∈ L.Q t, ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP h k =>
    not_mem_of_twist (hL.Q_pl t) h k
  refine ⟨Finset.disjoint_left.2 fun PP h h' => ?_, fun PP h => ?_, fun PP h j => ?_, fun P hP => ⟨?_, fun j => ?_⟩⟩
  · obtain ⟨k, hk⟩ := hPg PP h
    exact hQ PP h' k hk
  · obtain ⟨k, hk⟩ := hPg PP h
    by_contra hc
    rcases (hL.Q_ram t PP).1 hc with h' | ⟨PP', h', hc'⟩
    · exact hQ PP h' k hk
    · obtain ⟨q, hq, hq', hne⟩ :=
        GlobalTheory.StepLaw.exists_prime_mem_of_isTwistPlaces (hL.Q_pl t) h'
      exact GlobalTheory.StepLaw.not_two_primes_mem PP (D.host.g_prime k) hq (hne k).symm
        hk (natCast_mem_of_isConjPl hc' hq')
  · exact (L.C.isMu0 j).unr PP fun k => hQ PP h k
  · by_contra hc
    rcases (hL.Q_ram t P).1 hc with h' | ⟨PP', h', hc'⟩
    · exact hP P (Or.inr h') rfl
    · exact hP PP' (Or.inr h') (under_eq_of_isConjPl hc')
  · refine (L.C.isMu0 j).unr P fun k hk => ?_
    rcases div_or_div_conj L.C.P k P hk with h | h
    · exact hP P (Or.inl ((hL.Pg P).2 ⟨k, h⟩)) rfl
    · exact hP _ (Or.inl ((hL.Pg _).2 ⟨k, h⟩)) (under_eq_of_isConjPl (isConjPl_conjSpec P)).symm

end GlobalTheory
