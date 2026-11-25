module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private theorem step {p : ℕ} {A B C : CommRingCat} (u : A ⟶ B) (v : A ⟶ C) (FB : B ⟶ B) (FC : C ⟶ C)
    (r : B ⟶ C) (hB : ∀ x, FB x = x ^ p) (hC : ∀ x, FC x = x ^ p)
    (hU : v ≫ FC = (u ≫ FB) ≫ r) (a : A) : (u ≫ r).hom a ^ p = v.hom a ^ p := by
  have ha := ConcreteCategory.congr_hom hU a
  simp only [ConcreteCategory.comp_apply, hB, hC, map_pow] at ha
  simpa using ha.symm

private theorem frob_epi (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsReduced X]
    (h : (p : Γ(X, ⊤)) = 0) : Epi (GlobalTheory.VB.frob X p h) := by
  have hV (V : X.Opens) : (p : Γ(X, V)) = 0 := by
    have := congrArg (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom h
    simpa using this
  refine ⟨fun {Y} f g e => ?_⟩
  have hx (x : X) : f x = g x := by
    have := congrArg (fun φ : X ⟶ Y => φ x) e
    simpa [GlobalTheory.VB.frob, GlobalTheory.SS.FrobField.absFrob,
      GlobalTheory.SS.FrobField.absPre] using this
  refine Scheme.Hom.ext (by ext x; exact hx x) fun U => ?_
  have hU := Scheme.Hom.congr_app e.symm U
  rw [Scheme.Hom.comp_app, Scheme.Hom.comp_app] at hU
  ext a
  cases subsingleton_or_nontrivial Γ(X, g ⁻¹ᵁ U) with
  | inl _ => exact Subsingleton.elim _ _
  | inr _ =>
    have : CharP Γ(X, g ⁻¹ᵁ U) p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr (hV _)
    exact frobenius_inj Γ(X, g ⁻¹ᵁ U) p (step (p := p) (f.app U) (g.app U)
      ((GlobalTheory.VB.frob X p h).app (f ⁻¹ᵁ U)) ((GlobalTheory.VB.frob X p h).app (g ⁻¹ᵁ U)) _
      (GlobalTheory.VB.frob_app p h _) (GlobalTheory.VB.frob_app p h _) hU a)

theorem UpperTheory.Gal.Ord.epi :
    ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsReduced X] (h : (p : Γ(X, ⊤)) = 0), Epi (GlobalTheory.VB.frob X p h) ∧ ∀ j, Epi (frobN p X h j) := by
  intro p _ X _ h
  have hF := frob_epi p X h
  refine ⟨hF, fun j => ?_⟩
  induction j with
  | zero => exact (inferInstance : Epi (𝟙 X))
  | succ j ih =>
    have : Epi (frobN p X h j) := ih
    exact epi_comp (GlobalTheory.VB.frob X p h) (frobN p X h j)
