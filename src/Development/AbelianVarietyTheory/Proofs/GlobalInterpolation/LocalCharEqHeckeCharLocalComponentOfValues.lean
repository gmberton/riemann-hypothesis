module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

namespace GlobalTheory.LocCharComp

private theorem exists_zpow_uniformizer_factorization {E : Type} [Field E] [NumberField E]
    (P : HeightOneSpectrum (𝓞 E)) (π : 𝓞 E) (hπ : π ∈ P.asIdeal) (hπ2 : π ∉ P.asIdeal ^ 2)
    (a : E) (ha : a ≠ 0) :
    ∃ (z : ℤ) (r s : 𝓞 E), r ∉ P.asIdeal ∧ s ∉ P.asIdeal ∧
      algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r * algebraMap (𝓞 E) E π ^ z := by
  have hπ0 : π ≠ 0 := fun h => hπ2 (h ▸ Submodule.zero_mem _)
  have hlog : WithZero.log (P.intValuation π) = -1 := by
    have h1 : WithZero.exp (WithZero.log (P.intValuation π)) ≤ WithZero.exp (-(1 : ℕ) : ℤ) := by
      rw [WithZero.exp_log (P.intValuation_ne_zero π hπ0), P.intValuation_le_pow_iff_mem]
      simpa using hπ
    have h2 : ¬ WithZero.exp (WithZero.log (P.intValuation π)) ≤ WithZero.exp (-(2 : ℕ) : ℤ) := by
      rw [WithZero.exp_log (P.intValuation_ne_zero π hπ0), P.intValuation_le_pow_iff_mem]
      exact hπ2
    rw [WithZero.exp_le_exp] at h1 h2
    omega
  have hvπ : P.valuation E (algebraMap (𝓞 E) E π) = WithZero.exp (-1 : ℤ) := by
    rw [P.valuation_of_algebraMap, ← WithZero.exp_log (P.intValuation_ne_zero π hπ0), hlog]
  set z : ℤ := -WithZero.log (P.valuation E a)
  have hva : P.valuation E a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  have hx1 : P.valuation E (a / algebraMap (𝓞 E) E π ^ z) = 1 := by
    rw [map_div₀, map_zpow₀, hvπ, ← WithZero.exp_zsmul, zsmul_eq_mul, mul_neg_one, Int.cast_id]
    dsimp only [z]
    rw [neg_neg, WithZero.exp_log hva, div_self hva]
  obtain ⟨r, s, hrs⟩ := P.exists_primeCompl_mul_eq_of_integer _ hx1.le
  refine ⟨z, r, s.1, ?_, s.2, ?_⟩
  · rw [← P.valuation_eq_one_iff_notMem (K := E), ← hrs, map_mul, hx1, one_mul,
      P.valuation_eq_one_iff_notMem]
    exact s.2
  · have hpi : algebraMap (𝓞 E) E π ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 hπ0
    rw [← hrs, mul_right_comm, div_mul_cancel₀ _ (zpow_ne_zero z hpi), mul_comm]

private theorem exists_integer_ratio_of_isUnit_redP {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (b : E)
    (hb : IsUnit (redP P b)) :
    ∃ r s : 𝓞 E, r ∉ P.asIdeal ∧ s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * b = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * redP P b = Ideal.Quotient.mk P.asIdeal r := by
  have := P.isPrime
  unfold redP at hb ⊢
  split_ifs at hb ⊢ with h
  · obtain ⟨r, s, hs, hsb, hc⟩ := h.choose_spec
    refine ⟨r, s, fun hr => ?_, hs, hsb, hc⟩
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hr, hb.mul_left_eq_zero] at hc
    exact hs (Ideal.Quotient.eq_zero_iff_mem.1 hc)
  · exact absurd hb not_isUnit_zero

private theorem isUnit_redP_of_integer_ratio {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (b : E)
    (r s : 𝓞 E) (hr : r ∉ P.asIdeal) (hs : s ∉ P.asIdeal)
    (hsb : algebraMap (𝓞 E) E s * b = algebraMap (𝓞 E) E r) : IsUnit (redP P b) := by
  let := Ideal.Quotient.field P.asIdeal
  have hs' : Ideal.Quotient.mk P.asIdeal s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hex : ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧
      algebraMap (𝓞 E) E s * b = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r :=
    ⟨Ideal.Quotient.mk P.asIdeal r * (Ideal.Quotient.mk P.asIdeal s)⁻¹, r, s, hs, hsb,
      by rw [mul_comm (Ideal.Quotient.mk P.asIdeal r), ← mul_assoc, mul_inv_cancel₀ hs', one_mul]⟩
  unfold redP
  rw [dite_eq_left hex]
  obtain ⟨r₂, s₂, hs₂, hsb₂, hc₂⟩ := hex.choose_spec
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  rw [h0, mul_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem] at hc₂
  have he : s * r₂ = s₂ * r := IsFractionRing.injective (𝓞 E) E (by
    simp only [map_mul]
    rw [← hsb₂, ← hsb]
    ring)
  have hmem : s₂ * r ∈ P.asIdeal := he ▸ Ideal.mul_mem_left _ s hc₂
  exact (P.isPrime.mem_or_mem hmem).elim hs₂ hr

theorem locChar_eq_locK : ∀ (E K : Type) [Field E] [NumberField E] [Field K] (σ : K →+* ℂ) (P : HeightOneSpectrum (𝓞 E)) (ψ : Formalism.L2.Host.HChar E) (cq : K) (t : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ), ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → (∀ q : Eˣ, (q : E) = ((Ideal.absNorm P.asIdeal : ℕ) : E) → σ cq = ((ψ.locK P q : ℂˣ) : ℂ)) → (∀ (x : Eˣ) (y : 𝓞 E) (c : (𝓞 E ⧸ P.asIdeal)ˣ), (x : E) = (y : E) → (c : 𝓞 E ⧸ P.asIdeal) = Ideal.Quotient.mk P.asIdeal y → σ ((t c : Kˣ) : K) = ((ψ.locK P x : ℂˣ) : ℂ)) → ∀ a : Eˣ, σ (LocE.locChar (Formalism.L2.Col.qOf P) cq t (a : E)) = ((ψ.locK P a : ℂˣ) : ℂ) := by
  intro E K _ _ _ σ P ψ cq t hq2 h1 h2 a
  have := P.isPrime
  let := Ideal.Quotient.field P.asIdeal
  have hinj := IsFractionRing.injective (𝓞 E) E
  have hπ : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem _
  have hπE : ((qOf P : ℕ) : E) = algebraMap (𝓞 E) E ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) := by
    rw [map_natCast]
    rfl
  have hπne : ((qOf P : ℕ) : E) ≠ 0 := by
    rw [hπE]
    refine (map_ne_zero_iff _ hinj).2 fun h0 => hq2 ?_
    rw [h0]
    exact Submodule.zero_mem _
  have hex : ∃ z : ℤ, IsUnit (redP P ((a : E) / ((qOf P : ℕ) : E) ^ z)) := by
    obtain ⟨z, r, s, hr, hs, hsa⟩ := exists_zpow_uniformizer_factorization P _ hπ hq2 (a : E) a.ne_zero
    refine ⟨z, isUnit_redP_of_integer_ratio P _ r s hr hs ?_⟩
    rw [hπE, mul_div_assoc', hsa, mul_div_assoc, div_self (zpow_ne_zero _ (hπE ▸ hπne)), mul_one]
  have hU : IsUnit (redP P ((a : E) / ((qOf P : ℕ) : E) ^ LocE.vP P (qOf P) (a : E))) :=
    Classical.epsilon_spec hex
  obtain ⟨r, s, hr, hs, hsb, hc⟩ := exists_integer_ratio_of_isUnit_redP P _ hU
  have hr0 : algebraMap (𝓞 E) E r ≠ 0 := (map_ne_zero_iff _ hinj).2 fun h0 => hr (h0 ▸ Submodule.zero_mem _)
  have hs0 : algebraMap (𝓞 E) E s ≠ 0 := (map_ne_zero_iff _ hinj).2 fun h0 => hs (h0 ▸ Submodule.zero_mem _)
  have hmr : Ideal.Quotient.mk P.asIdeal r ≠ 0 := fun h => hr (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hms : Ideal.Quotient.mk P.asIdeal s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.1 h)
  set w := LocE.vP P (qOf P) (a : E)
  let Q : Eˣ := Units.mk0 _ hπne
  let xr : Eˣ := Units.mk0 _ hr0
  let xs : Eˣ := Units.mk0 _ hs0
  let cr : (𝓞 E ⧸ P.asIdeal)ˣ := Units.mk0 _ hmr
  let cs : (𝓞 E ⧸ P.asIdeal)ˣ := Units.mk0 _ hms
  have hA : a = Q ^ w * xr * xs⁻¹ := by
    ext
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, Units.val_mk0, Q, xr, xs]
    rw [← hsb]
    field_simp
  have hB : hU.unit = cr * cs⁻¹ := by
    ext
    simp only [IsUnit.unit_spec, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, cr, cs]
    rw [← hc]
    field_simp
  have eQ := h1 Q rfl
  have er := h2 xr r cr rfl rfl
  have es := h2 xs s cs rfl rfl
  show σ (cq ^ w * LocE.unitV t ((a : E) / ((qOf P : ℕ) : E) ^ w)) = _
  unfold LocE.unitV
  rw [dite_eq_left hU, hB]
  conv_rhs => rw [hA]
  simp only [map_mul, map_inv, map_zpow, map_zpow₀, Units.val_mul, Units.val_inv_eq_inv_val,
    Units.val_zpow_eq_zpow_val, map_inv₀, eQ, er, es]
  ring

end GlobalTheory.LocCharComp
