module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo

@[expose] public section

noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents GlobalTheory.IwahoriInj ValuativeRel

namespace GlobalTheory.JacInj

section Abstract

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π₁ : Representation ℂ G V} {π : Representation ℂ G W}

theorem map_apply' (f : π₁.IntertwiningMap π) (g : G) (v : V) : f (π₁ g v) = π g (f v) := by
  have h := LinearMap.congr_fun (f.isIntertwining' g) v
  simpa using h

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem mem_twKer_of_map (f : π₁.IntertwiningMap π) (hπ : IsSmooth π) (hf : Function.Injective f)
    {H : Subgroup G} (hH : IsCompact (H : Set G)) {v : V} (hv : f v ∈ twKer π H 1) :
    v ∈ twKer π₁ H 1 := by
  have h₁ : IsSmooth π₁ := by
    intro w
    have hset : {g : G | π₁ g w = w} = {g : G | π g (f w) = f w} := by
      ext g
      simp only [Set.mem_ofPred_eq, ← map_apply' f g w]
      exact hf.eq_iff.symm
    rw [hset]
    exact hπ (f w)
  obtain ⟨U, -, hU, hUv⟩ := GlobalTheory.LocGL.exists_normal_fix h₁ hH v
  letI : Fintype (H ⧸ U) := U.fintypeQuotientOfFiniteIndex
  have hUf : ∀ u ∈ U, π (u : H) (f v) = f v := fun u hu => by rw [← map_apply', hUv u hu]
  rw [← GlobalTheory.LocGL.idem_eq_zero_iff h₁ hH]
  apply hf

  rw [map_zero, GlobalTheory.LocGL.idem_eq_cosetSum h₁ hH U hUv, map_smul, map_sum]
  simp only [map_apply']
  rw [← GlobalTheory.LocGL.idem_eq_cosetSum hπ hH U hUf]
  exact (GlobalTheory.LocGL.idem_eq_zero_iff hπ hH).2 hv

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

def wt (e : (Σ a, m a) ≃ n) (M : ℕ) (i j : n) : ℤ :=
  M * (((Finset.univ.filter (· < blk e i)).card : ℤ) - (Finset.univ.filter (· < blk e j)).card)

theorem conc_wt (e : (Σ a, m a) ≃ n) (M : ℕ) : Conc (wt e M) := by
  unfold GlobalTheory.IwahoriInj.Conc
  refine ⟨fun i => by simp [wt], fun i j l => le_of_eq ?_⟩
  simp only [wt]
  ring

private theorem eventually_valuation_le_uniformizer_pow_of_mem_unipRad (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ unipRad k e) (i j : n) :
    ∀ᶠ M : ℕ in Filter.atTop, valuation k ((g : Matrix n n k) i j) ≤ uniformizer k ^ wt e M i j := by
  obtain ⟨hP, hD⟩ := mem_unipRad.1 hg
  rw [mem_parab] at hP
  rcases lt_trichotomy (blk e i) (blk e j) with h | h | h
  ·
    have hss : Finset.univ.filter (· < blk e i) ⊂ Finset.univ.filter (· < blk e j) :=
      (Finset.ssubset_iff_of_subset fun x hx => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact hx.trans h).2 ⟨blk e i, by simp [h], by simp⟩
    have hd : ((Finset.univ.filter (· < blk e i)).card : ℤ) -
        (Finset.univ.filter (· < blk e j)).card ≤ -1 := by
      have := Finset.card_lt_card hss; omega
    filter_upwards [eventually_deep ((g : Matrix n n k) i j)] with M hM
    exact hM.mono (by simp only [wt]; nlinarith [Int.natCast_nonneg M])
  ·
    refine Filter.Eventually.of_forall fun M => ?_
    have hw : wt e M i j = 0 := by simp [wt, h]
    rw [hw, zpow_zero]
    obtain ⟨⟨a, i'⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j
    simp only [blk_apply] at h
    cases h
    rw [hD _ i' j', Matrix.one_apply]
    split_ifs <;> simp
  ·
    exact Filter.Eventually.of_forall fun M => by
      rw [hP i j h, map_zero]
      exact zero_le'

theorem eventually_mem_grp (e : (Σ a, m a) ≃ n) {u : GL n k} (hu : u ∈ unipRad k e) :
    ∀ᶠ M : ℕ in Filter.atTop, u ∈ grp k (conc_wt e M) := by
  unfold GlobalTheory.IwahoriInj.grp
  simp only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq]
  unfold GlobalTheory.IwahoriInj.Deep
  have hu' : u⁻¹ ∈ unipRad k e := inv_mem hu
  exact (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_valuation_le_uniformizer_pow_of_mem_unipRad e hu i j).and
    (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_valuation_le_uniformizer_pow_of_mem_unipRad e hu' i j)

theorem isClosed_unipRad (e : (Σ a, m a) ≃ n) : IsClosed (unipRad k e : Set (GL n k)) := by
  have : T2Space k := (Model.secondCountable_and_t2_local_field (k := k)).2
  have hv : Continuous fun g : GL n k => (g : Matrix n n k) := Units.continuous_val
  have hc : ∀ i j, Continuous fun g : GL n k => (g : Matrix n n k) i j := fun i j => hv.matrix_elem i j
  have hset : (unipRad k e : Set (GL n k)) =
      {g : GL n k | ∀ i j, blk e j < blk e i → (g : Matrix n n k) i j = 0} ∩
        {g : GL n k | ∀ a (i j : m a), (g : Matrix n n k) (e ⟨a, i⟩) (e ⟨a, j⟩) = (1 : Matrix (m a) (m a) k) i j} := by
    ext g
    simp only [SetLike.mem_coe, mem_unipRad, mem_parab, Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [hset]
  refine IsClosed.inter ?_ ?_
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq (hc i j) continuous_const
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (hc _ _) continuous_const

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem eventually_mem_twKer_inf (e : (Σ a, m a) ≃ n) {π : Representation ℂ (GL n k) V} {v : V}
    (hv : v ∈ twKer π (unipRad k e) 1) :
    ∀ᶠ M : ℕ in Filter.atTop, v ∈ twKer π (grp k (conc_wt e M) ⊓ unipRad k e) 1 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, w, rfl⟩ := hx
    filter_upwards [eventually_mem_grp e u.2] with M hM
    exact Submodule.subset_span ⟨⟨u, hM, u.2⟩, w, rfl⟩
  | zero => exact Filter.Eventually.of_forall fun _ => Submodule.zero_mem _
  | add x y _ _ hx hy =>
    filter_upwards [hx, hy] with M h₁ h₂
    exact Submodule.add_mem _ h₁ h₂
  | smul c x _ hx =>
    filter_upwards [hx] with M h
    exact Submodule.smul_mem _ c h

theorem jacMap_injective (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
    (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL n k) V) (π : Representation ℂ (GL n k) W)
    (f : π₁.IntertwiningMap π) (hπ : IsSmooth π) (hf : Function.Injective f) :
    Function.Injective (jacMap e f) := by
  intro x y hxy
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hmk : ∀ u : V, jacMap e f (Submodule.Quotient.mk u) = Submodule.Quotient.mk (f u) :=
    fun _ => rfl
  rw [hmk, hmk, Submodule.Quotient.eq, ← map_sub] at hxy
  rw [Submodule.Quotient.eq]
  obtain ⟨M, hM⟩ := (eventually_mem_twKer_inf e hxy).exists
  have hcpt : IsCompact ((grp k (conc_wt e M) ⊓ unipRad k e : Subgroup (GL n k)) : Set (GL n k)) := by
    rw [Subgroup.coe_inf]
    exact (isCompact_grp (conc_wt e M)).inter_right (isClosed_unipRad e)
  exact _root_.GlobalTheory.IwahoriInj.twKer_mono inf_le_right (mem_twKer_of_map f hπ hf hcpt hM)

end GlobalTheory.JacInj
