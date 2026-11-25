module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBijectiveOfIsSubquotient
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleAlt
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.ProdLength

section General
variable {F G U V X : Type} [Field F] [Group G] [AddCommGroup U] [Module F U] [AddCommGroup V]
  [Module F V] [AddCommGroup X] [Module F X]

def comapSub {α : Representation F G U} {β : Representation F G V} (ι : α.IntertwiningMap β)
    (S : Subrepresentation β) : Subrepresentation α :=
  ⟨S.toSubmodule.comap ι.toLinearMap, fun g v hv => by
    show ι (α g v) ∈ S.toSubmodule
    rw [Representation.IntertwiningMap.isIntertwining]
    exact S.apply_mem_toSubmodule g hv⟩

def mapSub {β : Representation F G V} {γ : Representation F G X} (p : β.IntertwiningMap γ)
    (S : Subrepresentation β) : Subrepresentation γ :=
  ⟨S.toSubmodule.map p.toLinearMap, by
    rintro g _ ⟨v, hv, rfl⟩
    refine ⟨β g v, S.apply_mem_toSubmodule g hv, ?_⟩
    exact Representation.IntertwiningMap.isIntertwining _ _ p g v⟩

theorem hasFiniteLength_of_exact {α : Representation F G U} {β : Representation F G V}
    {γ : Representation F G X} (ι : α.IntertwiningMap β) (p : β.IntertwiningMap γ)
    (hex : ∀ v, p v = 0 → ∃ u, ι u = v) (hα : HasFiniteLength α) (hγ : HasFiniteLength γ) :
    HasFiniteLength β := by
  let ι' := Representation.IntertwiningMap.equivLinearMapAsModule α β ι
  let p' := Representation.IntertwiningMap.equivLinearMapAsModule β γ p
  have hK : LinearMap.ker p' ≤ LinearMap.range ι' := fun v hv =>
    hex v ((congrArg γ.asModuleEquiv hv).trans γ.asModuleEquiv.map_zero)
  have h1 : IsFiniteLength (MonoidAlgebra F G) (LinearMap.ker p') :=
    (IsFiniteLength.of_surjective hα ι'.surjective_rangeRestrict).of_injective
      (Submodule.inclusion_injective hK)
  have h2 : IsFiniteLength (MonoidAlgebra F G) (β.asModule ⧸ LinearMap.ker p') :=
    p'.quotKerEquivRange.symm.isFiniteLength
      (IsFiniteLength.of_injective hγ (Submodule.injective_subtype (LinearMap.range p')))
  obtain ⟨h1n, h1a⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp h1
  obtain ⟨h2n, h2a⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp h2
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨(isNoetherian_iff_submodule_quotient (LinearMap.ker p')).mpr ⟨h1n, h2n⟩,
      (isArtinian_iff_submodule_quotient (LinearMap.ker p')).mpr ⟨h1a, h2a⟩⟩

theorem hasFiniteLength_of_injective {α : Representation F G U} {β : Representation F G V}
    (ι : α.IntertwiningMap β) (hι : Function.Injective ι) (hβ : HasFiniteLength β) :
    HasFiniteLength α :=
  IsFiniteLength.of_injective hβ
    (f := Representation.IntertwiningMap.equivLinearMapAsModule α β ι) hι

theorem hasFiniteLength_of_subsingleton [Subsingleton V] (β : Representation F G V) :
    HasFiniteLength β := by
  haveI : Subsingleton β.asModule := β.asModuleEquiv.toEquiv.subsingleton
  exact IsFiniteLength.of_subsingleton

end General

section Tensor
open GlobalTheory.ParIndExact
variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem hasFiniteLength_extTensor_left (A : Representation ℂ G V) (B : Representation ℂ H W)
    (hA : HasFiniteLength A)
    (hbase : ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (σ : Representation ℂ G Y), σ.IsIrreducible →
      IsSubquotient σ A → HasFiniteLength (extTensor σ B)) :
    HasFiniteLength (extTensor A B) := by
  obtain ⟨h1, h2⟩ := (hasFiniteLength_iff_wellFounded A).1 hA
  have key : ∀ S T : Subrepresentation A, T ≤ S → HasFiniteLength (extTensor (subQuot S T) B) := by
    intro S₀
    refine WellFoundedLT.induction (motive := fun S => ∀ T, T ≤ S →
      HasFiniteLength (extTensor (subQuot S T) B)) S₀ ?_
    intro S ihS T₀
    refine WellFoundedGT.induction (motive := fun T => T ≤ S →
      HasFiniteLength (extTensor (subQuot S T) B)) T₀ ?_
    intro T ihT hTS
    rcases eq_or_lt_of_le hTS with hEq | hlt
    · subst hEq
      haveI := subsingleton_subQuot_self T
      haveI := tensor_subsingleton_left (F := ℂ)
        (V := ↥T.toSubmodule ⧸ Submodule.comap T.toSubmodule.subtype T.toSubmodule) (W := W)
      exact hasFiniteLength_of_subsingleton _
    by_cases hc : T ⋖ S
    · exact hbase _ _ (isIrreducible_subQuot hc) (isSubquotient_subQuot S T)
    obtain ⟨U, hTU, hUS⟩ : ∃ U, T < U ∧ U < S := by
      by_contra hno
      exact hc ⟨hlt, fun U h1 h2 => hno ⟨U, h1, h2⟩⟩
    obtain ⟨ι, p, hι, hp, hpι, hex⟩ := subQuot_exact (ρ := A) hTU.le hUS.le
    obtain ⟨ι', p', -, hex'⟩ := extTensor_exact_left B ι p hι hp hpι hex
    exact hasFiniteLength_of_exact ι' p' hex' (ihS U hUS T hTU.le) (ihT U hTU hUS.le)
  obtain ⟨ι, hι⟩ := subQuot_top_bot A
  obtain ⟨ι', hι'⟩ := extTensor_injective_left B ι hι
  exact hasFiniteLength_of_injective ι' hι' (key ⊤ ⊥ bot_le)

theorem hasFiniteLength_extTensor_right (A : Representation ℂ G V) (B : Representation ℂ H W)
    (hB : HasFiniteLength B)
    (hbase : ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ H Y), τ.IsIrreducible →
      IsSubquotient τ B → HasFiniteLength (extTensor A τ)) :
    HasFiniteLength (extTensor A B) := by
  obtain ⟨h1, h2⟩ := (hasFiniteLength_iff_wellFounded B).1 hB
  have key : ∀ S T : Subrepresentation B, T ≤ S → HasFiniteLength (extTensor A (subQuot S T)) := by
    intro S₀
    refine WellFoundedLT.induction (motive := fun S => ∀ T, T ≤ S →
      HasFiniteLength (extTensor A (subQuot S T))) S₀ ?_
    intro S ihS T₀
    refine WellFoundedGT.induction (motive := fun T => T ≤ S →
      HasFiniteLength (extTensor A (subQuot S T))) T₀ ?_
    intro T ihT hTS
    rcases eq_or_lt_of_le hTS with hEq | hlt
    · subst hEq
      haveI := subsingleton_subQuot_self T
      haveI := tensor_subsingleton_right (F := ℂ) (V := V)
        (W := ↥T.toSubmodule ⧸ Submodule.comap T.toSubmodule.subtype T.toSubmodule)
      exact hasFiniteLength_of_subsingleton _
    by_cases hc : T ⋖ S
    · exact hbase _ _ (isIrreducible_subQuot hc) (isSubquotient_subQuot S T)
    obtain ⟨U, hTU, hUS⟩ : ∃ U, T < U ∧ U < S := by
      by_contra hno
      exact hc ⟨hlt, fun U h1 h2 => hno ⟨U, h1, h2⟩⟩
    obtain ⟨ι, p, hι, hp, hpι, hex⟩ := subQuot_exact (ρ := B) hTU.le hUS.le
    obtain ⟨ι', p', -, hex'⟩ := extTensor_exact_right A ι p hι hp hpι hex
    exact hasFiniteLength_of_exact ι' p' hex' (ihS U hUS T hTU.le) (ihT U hTU hUS.le)
  obtain ⟨ι, hι⟩ := subQuot_top_bot B
  obtain ⟨ι', hι'⟩ := extTensor_injective_right A ι hι
  exact hasFiniteLength_of_injective ι' hι' (key ⊤ ⊥ bot_le)

end Tensor
end GlobalTheory.ProdLength

theorem GlobalTheory.ProdLength.prod₂_hasFiniteLength : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W), HasFiniteLength π₁ → HasFiniteLength π₂ → IsSmooth π₁ → IsSmooth π₂ → HasFiniteLength (prod₂ π₁ π₂) := by
  intro hBZ k _ _ _ _ r t V W _ _ _ _ π₁ π₂ h₁ h₂ s₁ s₂
  obtain ⟨hAdm, -, hInd, -⟩ := hBZ k
  have schur : ∀ (n : ℕ) (Y : Type) [AddCommGroup Y] [Module ℂ Y] (σ : Representation ℂ (GL (Fin n) k) Y),
      IsSmooth σ → σ.IsIrreducible → ∀ φ : Y →ₗ[ℂ] Y, (∀ g x, φ (σ g x) = σ g (φ x)) →
        ∃ c : ℂ, φ = c • LinearMap.id := fun n Y _ _ σ hs hi =>
    _root_.GlobalTheory.SchurAdmissibility.schur_admissible _ (KO k (Fin n)) GlobalTheory.SplitFlip.isOpen_KO GlobalTheory.SplitFlip.isCompact_KO Y σ hi
      (hAdm (Fin n) Y σ hs hi)
  have hT : HasFiniteLength (extTensor π₁ π₂) :=
    GlobalTheory.ProdLength.hasFiniteLength_extTensor_left π₁ π₂ h₁ fun Y _ _ σ hσ hsq =>
      GlobalTheory.ProdLength.hasFiniteLength_extTensor_right σ π₂ h₂ fun Z _ _ τ hτ hsq' =>
        hasFiniteLength_of_isIrreducible (GlobalTheory.JacFactor.isIrreducible_extTensor σ τ hσ hτ
          (schur r Y σ (hsq.isSmooth s₁) hσ) (schur t Z τ (hsq'.isSmooth s₂) hτ))
  have hc : Continuous (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom :=
    (continuous_apply false).prodMk (continuous_apply true)
  exact hInd Bool (Fin (r + t)) (Two (Fin r) (Fin t)) (two (stdSum rfl)) _ _
    (isSmooth_comp (isSmooth_extTensor s₁ s₂) _ hc)
    ((hasFiniteLength_comp_iff _ _ (leviTwo k (Fin r) (Fin t)).symm.surjective).2 hT)
