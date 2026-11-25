module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightWittEmbeddingLeConstMul
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix

noncomputable section

namespace GlobalTheory.EmbHeight

open scoped NNReal TensorProduct
open NumberField IsDedekindDomain GlobalTheory.AdelicU Formalism.UG

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]


open scoped Matrix.Norms.L2Operator in
theorem exists_opNorm_le (J : Matrix n m ℂ) (P : Matrix m n ℂ) (K : Matrix n n ℂ) :
    ∃ c : ℝ≥0, ∀ (x : Matrix m m ℂ) (h : ℝ≥0), 1 ≤ h → opNorm x ≤ h → opNorm (J * x * P + K) ≤ c * h := by
  refine ⟨‖J‖₊ * ‖P‖₊ + ‖K‖₊, fun x h h1 hx => ?_⟩
  have hx' : ‖x‖₊ ≤ h := hx
  calc opNorm (J * x * P + K) = ‖J * x * P + K‖₊ := rfl
    _ ≤ ‖J * x * P‖₊ + ‖K‖₊ := nnnorm_add_le _ _
    _ ≤ ‖J‖₊ * ‖x‖₊ * ‖P‖₊ + ‖K‖₊ := by
        gcongr
        exact (Matrix.l2_opNNNorm_mul _ _).trans (by gcongr; exact Matrix.l2_opNNNorm_mul _ _)
    _ ≤ ‖J‖₊ * h * ‖P‖₊ + ‖K‖₊ * h := by
        gcongr
        exact le_mul_of_one_le_right (by positivity) h1
    _ = (‖J‖₊ * ‖P‖₊ + ‖K‖₊) * h := by ring

theorem htOf_le {R : Type} [CommRing R] {N₁ : Matrix m m R → ℝ≥0} {N : Matrix n n R → ℝ≥0}
    {f : Matrix m m R → Matrix n n R} {c : ℝ≥0} (hc : 1 ≤ c)
    (hN : ∀ (x : Matrix m m R) (h : ℝ≥0), 1 ≤ h → N₁ x ≤ h → N (f x) ≤ c * h)
    (X : GL n R) (x : GL m R) (h1 : (X : Matrix n n R) = f x)
    (h2 : ((X⁻¹ : GL n R) : Matrix n n R) = f (x⁻¹ : GL m R)) : htOf N X ≤ c * htOf N₁ x := by
  exact htOf_le_mul hc X x
    (by rw [h1]; exact hN _ _ (le_max_left _ _) (le_max_right _ _))
    (by rw [h2]; exact hN _ _ (le_max_left _ _) (le_max_right _ _))

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem exists_normInf_le (w : InfinitePlace F) (J : Matrix n m (w.Completion ⊗[F] E))
    (P : Matrix m n (w.Completion ⊗[F] E)) (K : Matrix n n (w.Completion ⊗[F] E)) :
    ∃ c : ℝ≥0, 1 ≤ c ∧ ∀ (x : Matrix m m (w.Completion ⊗[F] E)) (h : ℝ≥0), 1 ≤ h → normInf F w x ≤ h →
      normInf F w (J * x * P + K) ≤ c * h := by
  classical
  have hτ : ∀ τ : EmbOver E w, ∃ c : ℝ≥0, ∀ (x : Matrix m m ℂ) (h : ℝ≥0), 1 ≤ h → opNorm x ≤ h →
      opNorm (J.map (infEmb τ) * x * P.map (infEmb τ) + K.map (infEmb τ)) ≤ c * h :=
    fun τ => GlobalTheory.EmbHeight.exists_opNorm_le _ _ _
  choose c hc using hτ
  refine ⟨max 1 (Finset.univ.sup c), le_max_left _ _, fun x h h1 hx => ?_⟩
  rw [normInf_le_iff] at hx ⊢
  intro τ
  rw [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul]
  refine (hc τ _ h h1 (hx τ)).trans ?_
  gcongr
  exact (Finset.le_sup (Finset.mem_univ τ)).trans (le_max_right _ _)

omit [DecidableEq m] [DecidableEq n] in
theorem normFin_le (v : HeightOneSpectrum (𝓞 F)) (J : Matrix n m (Fv F v ⊗[F] E))
    (P : Matrix m n (Fv F v ⊗[F] E)) (K : Matrix n n (Fv F v ⊗[F] E))
    (x : Matrix m m (Fv F v ⊗[F] E)) (h : ℝ≥0) (h1 : 1 ≤ h) (hx : normFin F v x ≤ h) :
    normFin F v (J * x * P + K) ≤ max 1 (max (normFin F v J * normFin F v P) (normFin F v K)) * h := by
  classical
  calc normFin F v (J * x * P + K) = normFin F v (K + J * x * P) := by rw [add_comm]
    _ ≤ max 1 (max (normFin F v K) (normFin F v J * normFin F v P)) * max 1 (normFin F v x) :=
        normFin_aff_le F v K J P x
    _ ≤ _ := by rw [max_comm (normFin F v K)]; exact mul_le_mul' le_rfl (max_le h1 hx)


omit [DecidableEq m] [DecidableEq n] in
theorem eventually_normFin_le (y : Matrix m n (AF F ⊗[F] E)) :
    ∀ᶠ v in Filter.cofinite, normFin F v (y.map (compFin F E v)) ≤ 1 := by
  exact eventually_normFin_rect_le_one F y

theorem exists_heightGL_le (J : Matrix n m (AF F ⊗[F] E)) (P : Matrix m n (AF F ⊗[F] E))
    (K : Matrix n n (AF F ⊗[F] E)) :
    ∃ C : ℝ≥0, ∀ (X : GL n (AF F ⊗[F] E)) (x : GL m (AF F ⊗[F] E)),
      (X : Matrix n n (AF F ⊗[F] E)) = J * (x : Matrix m m (AF F ⊗[F] E)) * P + K →
      ((X⁻¹ : GL n (AF F ⊗[F] E)) : Matrix n n (AF F ⊗[F] E)) =
        J * ((x⁻¹ : GL m (AF F ⊗[F] E)) : Matrix m m (AF F ⊗[F] E)) * P + K →
      heightGL F X ≤ C * heightGL F x := by
  obtain ⟨C, hC⟩ := exists_heightGL_aff_le F K J P
  exact ⟨C, fun X x hX hXi =>
    hC X x (hX.trans (add_comm _ _)) (hXi.trans (add_comm _ _))⟩

theorem height_emb_le : ∀ (D : D7) (S A B : HSp D) (o : GlobalTheory.MixModel.OrthDec S A B), ∃ (C : ℝ) (a : ℕ),
    ∀ g : GA D A, GlobalTheory.Grow.height S (o.emb (g, 1)) ≤ C * GlobalTheory.Grow.height A g ^ a := by
  intro D S A B o
  obtain ⟨C, hC⟩ := GlobalTheory.EmbHeight.exists_heightGL_le D.host.F o.jA o.pA (o.jB * o.pB)
  refine ⟨(C : ℝ), 1, fun g => ?_⟩
  have e : ∀ a : GA D A, (Formalism.L2.Theta.matHom S (o.emb (a, 1)) :
      Matrix (Fin S.rank) (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) =
      o.jA * (Formalism.L2.Theta.matHom A a : Matrix (Fin A.rank) (Fin A.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) *
        o.pA + o.jB * o.pB := by
    intro a
    have hm := o.mt_emb a 1
    rw [GlobalTheory.MixModel.mt_one, Matrix.mul_one] at hm
    exact hm
  have hinv : o.emb (g⁻¹, 1) = (o.emb (g, 1))⁻¹ := by
    rw [← map_inv, Prod.inv_mk, inv_one]
  have e2 := e g⁻¹
  rw [hinv, map_inv, map_inv] at e2
  have key := hC _ _ (e g) e2
  unfold GlobalTheory.Grow.height
  rw [pow_one]
  exact_mod_cast key

end GlobalTheory.EmbHeight

end
