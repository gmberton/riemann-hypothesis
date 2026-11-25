module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.FinrankK
import Development.DiscreteGroups.GlobalIrreducibility.DzApprox
import Development.DiscreteGroups.GlobalIrreducibility.DzGalRes
import Development.DiscreteGroups.GlobalIrreducibility.DzIneEq
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

theorem UpperTheory.Zero.LLC.typeIff :
    UpperTheory.Zero.LLC.TypeIff := by
  intro E Ω _ _ _ _ _ A w h rc
  constructor
  · intro H x g _ i hi n hn D R hR θ hθ τ hτ hNm σ hσ hinf
    subst hσ
    have main := H D.E' g D.w' D.h' i hi n hn D.unr D.card D.a' D.ha' D.K D.red D.surj D.ker θ hθ τ hτ hNm σ hinf
    refine ⟨main.1, fun t => ?_⟩
    obtain ⟨t', ht', e⟩ := DiscreteGroups.sglob.DzType.ine_lift g A w h D.w' D.h' n hn D.unr D.card (t : G E Ω) t.2
    obtain ⟨x, hx⟩ := DiscreteGroups.sglob.DzType.exists_int_approx_compl D.w' _
      (DiscreteGroups.sglob.DzType.val_artin_ine D.ha' (⟨t', ht'⟩ : Ine (F := D.E') A)).le
    have hne := DiscreteGroups.sglob.DzType.red_ne_zero_of_approx D.ha' D.ker hx
    have hz : R t = Units.mk0 (D.red x) hne := hR t ⟨t', ht'⟩ x _ e.symm rfl hx
    have key := main.2 ⟨t', ht'⟩ x (Units.mk0 _ hne) rfl hx
    rw [hz, ← e]
    exact key
  · intro H E' _ _ _ _ _ _ g _ w' h' i hi n hn unr card a' ha' K _ _ red surj ker θ hθ τ hτ hNm σ hinf
    let D : Ext h g n :=
      { E' := E', w' := w', h' := h', unr := unr, card := card, a' := a', ha' := ha', K := K, red := red,
        surj := surj, ker := ker }
    obtain ⟨R, hR⟩ := (UpperTheory.Zero.LLC.resEx E Ω A w h g i hi n hn D).1
    have main := H (cls σ) g i hi n hn D R hR θ hθ τ hτ hNm σ rfl hinf
    refine ⟨main.1, fun t x z hz hx => ?_⟩
    have hm : AlgEquiv.restrictScalars E (t : G E' Ω) ∈ Ine (F := E) A :=
      GlobalTheory.AboveL.ResEx.res_mem_Ine t.2
    have e : R ⟨_, hm⟩ = z := hR ⟨_, hm⟩ t x z rfl hz hx
    have key := main.2 ⟨_, hm⟩
    rw [e] at key
    exact key

end
