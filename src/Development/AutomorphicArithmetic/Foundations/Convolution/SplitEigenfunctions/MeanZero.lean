module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.GrpEqMemArchCompact
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.AbLower
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ContinuousPrN
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.DiagInvVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeL2InnerProduct
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieSkewAdjointL2

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical Pointwise

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.MZ

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

private theorem bdd (hD : DecE) (hR : RedE) (P : CuspSub E 2) {φ : Sm E 2} (hφ : φ ∈ P.V) {C : Set (GL (Fin 2) (A E))} (hC : IsCompact C) :
    ∃ B : ℝ, ∀ h : G1 E, ∀ k ∈ C, ‖φ.1 (gl h * k)‖ ≤ B := by
  obtain ⟨c, C₀, hc, hC₀, hred⟩ := hR E
  obtain ⟨hL, -, hdec⟩ := hD E P φ hφ
  obtain ⟨B, hB⟩ := hdec ((gl '' C₀) * C) ((hC₀.image continuous_gl).mul hC) c hc 0
  refine ⟨B, fun h k hk => ?_⟩
  obtain ⟨γ, u, b, k₀, hk₀, he, hb⟩ := hred h
  have h1 : φ.1 (gl h * k) = φ.1 (gl (nU u * mD b) * (gl k₀ * k)) := by
    rw [← hL.2 (Matrix.SpecialLinearGroup.toGL γ) (gl h * k), ← gl_ratS, ← mul_assoc,
      ← mul_assoc, ← map_mul, he, map_mul]
  rw [h1]
  simpa using hB u b _ (Set.mul_mem_mul ⟨k₀, hk₀, rfl⟩ hk) hb

private theorem integ (N : MeasE E) (hfin : N.μ N.D < ⊤) {f : G1 E → ℂ} (hf : Continuous f) {B : ℝ} (hB : ∀ h, ‖f h‖ ≤ B) :
    IntegrableOn f N.D N.μ :=
  Measure.integrableOn_of_bounded hfin.ne hf.aestronglyMeasurable (Eventually.of_forall hB)

private theorem lie_zero (hD : DecE) (hR : RedE) (N : MeasE E) (hfin : N.μ N.D < ⊤) (P : CuspSub E 2) {φ : Sm E 2} (hφ : φ ∈ P.V)
    (h0 : ∀ y, ∫ h in N.D, φ.1 (gl h * y) ∂N.μ = 0) (X : Lie E 2) (y : GL (Fin 2) (A E)) :
    ∫ h in N.D, (lie E 2 X φ).1 (gl h * y) ∂N.μ = 0 := by
  set c := GlobalTheory.ExpDeriv.expGL X
  have ccont : Continuous fun t => infGL E 2 (c t) := by
    have heq : c = GlobalTheory.CompanionTheory.LieCurve.expUnit E 2 (Matrix.of X) :=
      funext fun t => Units.ext ((GlobalTheory.ExpDeriv.expGL_val X t).trans
        (GlobalTheory.CompanionTheory.LieCurve.expUnit_val E 2 (Matrix.of X) t).symm)
    rw [heq]
    exact (GlobalTheory.CompanionTheory.LieSkew.continuous_infGL_map E 2).comp
      (GlobalTheory.CompanionTheory.LieCurve.continuous_expUnit E 2 _)
  have hψ : lie E 2 X φ ∈ P.V := P.stable (.lie X) φ hφ
  have hCc : IsCompact ((fun t : ℝ => y * infGL E 2 (c t)) '' Set.Icc (-1) 1) := isCompact_Icc.image (continuous_const.mul ccont)
  obtain ⟨B, hB⟩ := bdd hD hR P hψ hCc
  obtain ⟨B', hB'⟩ := bdd hD hR P hφ hCc
  have cφ : ∀ z, Continuous fun h : G1 E => φ.1 (gl h * z) :=
    fun z => (hD E P φ hφ).1.1.comp (continuous_gl.mul continuous_const)
  have cψ : ∀ z, Continuous fun h : G1 E => (lie E 2 X φ).1 (gl h * z) :=
    fun z => (hD E P _ hψ).1.1.comp (continuous_gl.mul continuous_const)
  have hz : y * infGL E 2 (c 0) = y := by
    rw [show c 0 = 1 from GlobalTheory.ExpDeriv.expGL_zero X, map_one, mul_one]
  have h0m : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
  haveI : IsFiniteMeasure (N.μ.restrict N.D) := ⟨by simpa using hfin⟩
  have hb := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := N.μ.restrict N.D)
    (F := fun t h => φ.1 (gl h * (y * infGL E 2 (c t)))) (F' := fun t h => (lie E 2 X φ).1 (gl h * (y * infGL E 2 (c t))))
    (x₀ := (0 : ℝ)) (bound := fun _ => B) (s := Set.Ioo (-1) 1) (Ioo_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall fun t => (cφ _).aestronglyMeasurable)
    (integ N hfin (cφ _) fun h => hB' h _ ⟨0, h0m, rfl⟩)
    (cψ _).aestronglyMeasurable
    (Eventually.of_forall fun h t ht => hB h _ ⟨t, Set.Ioo_subset_Icc_self ht, rfl⟩)
    (integrable_const _)
    (Eventually.of_forall fun h t _ => by
      simpa only [mul_assoc] using GlobalTheory.ExpDeriv.hasDerivAt_along X φ (gl h * y) t)
  have e : (fun t : ℝ => ∫ h in N.D, φ.1 (gl h * (y * infGL E 2 (c t))) ∂N.μ) = fun _ => 0 := funext fun t => h0 _
  have := hb.2
  rw [e, hz] at this
  exact this.unique (hasDerivAt_const _ _)

private def Ker (N : MeasE E) (P : CuspSub E 2) (hI : ∀ φ ∈ P.V, ∀ y, IntegrableOn (fun h : G1 E => φ.1 (gl h * y)) N.D N.μ) :
    Submodule ℂ (Sm E 2) where
  carrier := {φ | φ ∈ P.V ∧ ∀ y, ∫ h in N.D, φ.1 (gl h * y) ∂N.μ = 0}
  add_mem' := fun {a b} ha hb => ⟨P.V.add_mem ha.1 hb.1, fun y => by
    change ∫ h in N.D, (a.1 (gl h * y) + b.1 (gl h * y)) ∂N.μ = 0
    rw [integral_add (hI a ha.1 y) (hI b hb.1 y), ha.2, hb.2, add_zero]⟩
  zero_mem' := ⟨P.V.zero_mem, fun y => by
    change ∫ h in N.D, (0 : ℂ) ∂N.μ = 0
    simp⟩
  smul_mem' := fun c a ha => ⟨P.V.smul_mem c ha.1, fun y => by
    change ∫ h in N.D, c * a.1 (gl h * y) ∂N.μ = 0
    rw [integral_const_mul, ha.2, mul_zero]⟩

private theorem ker_stable (hD : DecE) (hR : RedE) (N : MeasE E) (hfin : N.μ N.D < ⊤) (P : CuspSub E 2) (hI) :
    _root_.GlobalTheory.CuspRep.IsStable (Ker N P hI) := by
  intro o φ hφ
  refine ⟨P.stable o φ hφ.1, fun y => ?_⟩
  cases o with
  | fin k =>
    change ∫ h in N.D, φ.1 (gl h * y * finGL E 2 k) ∂N.μ = 0
    simpa only [mul_assoc] using hφ.2 (y * finGL E 2 k)
  | cpt k =>
    change ∫ h in N.D, φ.1 (gl h * y * infGL E 2 (Unitary.toUnits k)) ∂N.μ = 0
    simpa only [mul_assoc] using hφ.2 (y * infGL E 2 (Unitary.toUnits k))
  | lie X => exact lie_zero hD hR N hfin P hφ.1 hφ.2 X y

private theorem mean_det (hV : InvE) (N : MeasE E) {φ : Sm E 2} (hL : Pp.Lf φ.1) (y w : GL (Fin 2) (A E))
    (hw : Matrix.GeneralLinearGroup.det w = 1) :
    ∫ h in N.D, φ.1 (gl h * (w * y)) ∂N.μ = ∫ h in N.D, φ.1 (gl h * y) ∂N.μ := by
  obtain ⟨w', rfl⟩ := exists_gl_of_det_eq_one w hw
  have hLR : LRat fun x => φ.1 (x * y) := fun γ g => by
    change φ.1 (ratGL E 2 γ * g * y) = φ.1 (g * y)
    rw [mul_assoc, hL.2]
  simpa only [mean, mul_assoc] using ((hV E N).2 _ hLR).1 w'

private theorem fixed (hV : InvE) (N : MeasE E) (P : CuspSub E 2) (hI) (hL : ∀ φ ∈ P.V, Pp.Lf φ.1) (hK : Ker N P hI = ⊥) {φ : Sm E 2} (hφ : φ ∈ P.V)
    (k : GL (Fin 2) (Af E)) (hk : Matrix.GeneralLinearGroup.det (finGL E 2 k) = 1) (g : GL (Fin 2) (A E)) :
    φ.1 (g * finGL E 2 k) = φ.1 g := by
  have hm : finRep E 2 k φ ∈ P.V := P.stable (.fin k) φ hφ
  have hmem : finRep E 2 k φ - φ ∈ Ker N P hI := by
    refine ⟨P.V.sub_mem hm hφ, fun y => ?_⟩
    change ∫ h in N.D, (φ.1 (gl h * y * finGL E 2 k) - φ.1 (gl h * y)) ∂N.μ = 0
    have e : ∀ h : G1 E, gl h * y * finGL E 2 k = gl h * ((y * finGL E 2 k * y⁻¹) * y) := fun h => by group
    have hw : Matrix.GeneralLinearGroup.det (y * finGL E 2 k * y⁻¹) = 1 := by
      rw [map_mul, map_mul, hk, mul_one, map_inv, mul_inv_cancel]
    rw [integral_sub (by simp only [e]; exact hI _ hφ ((y * finGL E 2 k * y⁻¹) * y)) (hI φ hφ y)]
    simp only [e]
    rw [mean_det hV N (hL φ hφ) y _ hw, sub_self]
  rw [hK, Submodule.mem_bot] at hmem
  have := congrFun (congrArg Subtype.val hmem) g
  exact sub_eq_zero.1 this

private noncomputable def iI (x : InfiniteAdeleRing E) : A E := (x, 0)

private theorem cont_iI : Continuous (iI : InfiniteAdeleRing E → A E) :=
  (continuous_id.prodMk continuous_const : Continuous fun x : InfiniteAdeleRing E => ((x, 0) : InfiniteAdeleRing E × Af E))

private theorem gl_nU_fin (a : Af E) : ∃ k, gl (nU (sFin E a)) = finGL E 2 k := by
  refine ⟨Matrix.GeneralLinearGroup.map (pFin E) (gl (nU (sFin E a))), ?_⟩
  have h1 : Matrix.GeneralLinearGroup.map (pInf E) (gl (nU (sFin E a))) = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    have h0 : pInf E (sFin E a) = 0 := map_zero (infEq E).symm
    change pInf E ((gl (nU (sFin E a))).val i j) = (1 : Matrix (Fin 2) (Fin 2) (Cinf E)) i j
    rw [show (gl (nU (sFin E a))).val i j = (!![1, sFin E a; 0, 1] : Matrix (Fin 2) (Fin 2) (A E)) i j from rfl]
    fin_cases i <;> fin_cases j <;> simp [h0]
  have := infGL_mul_finGL (gl (nU (sFin E a)))
  rw [h1, map_one, one_mul] at this
  exact this.symm

private theorem left_inv {φ : Sm E 2} (hL : Pp.Lf φ.1)
    (hfix : ∀ k, Matrix.GeneralLinearGroup.det (finGL E 2 k) = 1 → ∀ g, φ.1 (g * finGL E 2 k) = φ.1 g) (b : A E) (g : GL (Fin 2) (A E)) :
    φ.1 (gl (nU b) * g) = φ.1 g := by
  set S : AddSubgroup (A E) :=
    { carrier := {b | ∀ g, φ.1 (gl (nU b) * g) = φ.1 g}
      add_mem' := fun {x y} hx hy g => by rw [M.nU_add, gl_mul, mul_assoc, hx, hy]
      zero_mem' := fun g => by rw [M.nU_zero, gl_one, one_mul]
      neg_mem' := fun {x} hx g => by
        have := hx (gl (nU (-x)) * g)
        rw [← mul_assoc, ← gl_mul, ← M.nU_add, add_neg_cancel, M.nU_zero, gl_one, one_mul] at this
        exact this.symm } with hS
  have hq : ∀ q : E, rt q ∈ S := fun q g => by
    obtain ⟨γ, hγ⟩ := nU_rt_mem q
    rw [← hγ, gl_ratS]
    exact hL.2 _ g
  have hf : ∀ a : Af E, sFin E a ∈ S := fun a g => by
    obtain ⟨k₀, e⟩ := gl_nU_fin a
    set u := Matrix.GeneralLinearGroup.map (pFin E) g
    set y := Matrix.GeneralLinearGroup.map (pInf E) g
    have hg : infGL E 2 y * finGL E 2 u = g := infGL_mul_finGL g
    have e1 : g * finGL E 2 (u⁻¹ * k₀ * u) = finGL E 2 k₀ * g := by
      rw [map_mul, map_mul, map_inv]
      nth_rw 1 [← hg]
      rw [← mul_assoc, ← mul_assoc, mul_assoc (infGL E 2 y), mul_inv_cancel, mul_one, infGL_comm, mul_assoc, hg]
    have hd : Matrix.GeneralLinearGroup.det (finGL E 2 k₀) = 1 := by
      rw [← e]
      exact Units.ext (nU (sFin E a)).2
    have hd' : Matrix.GeneralLinearGroup.det (finGL E 2 (u⁻¹ * k₀ * u)) = 1 := by
      simp only [map_mul, map_inv, hd, mul_one, inv_mul_cancel]
    rw [e, ← e1]
    exact hfix _ hd' g
  have hinf : ∀ x : InfiniteAdeleRing E, iI x ∈ S := by
    intro x
    refine (InfiniteAdeleRing.denseRange_algebraMap E).induction_on (p := fun x => iI x ∈ S) x ?_ ?_
    · have : {x : InfiniteAdeleRing E | iI x ∈ S} = ⋂ g, {x | φ.1 (gl (nU (iI x)) * g) = φ.1 g} :=
        Set.ext fun x => ⟨fun h => Set.mem_iInter.2 h, fun h => Set.mem_iInter.1 h⟩
      rw [this]
      exact isClosed_iInter fun g =>
        isClosed_eq (hL.1.comp ((continuous_gl.comp (M.continuous_nU.comp cont_iI)).mul
          continuous_const)) continuous_const
    · intro q
      have e : rt q = iI (algebraMap E (InfiniteAdeleRing E) q) + sFin E (algebraMap E (Af E) q) :=
        Prod.ext (add_zero _).symm (zero_add _).symm
      rw [eq_sub_of_add_eq e.symm]
      exact S.sub_mem (hq q) (hf _)
  have e : b = iI b.1 + sFin E b.2 := Prod.ext (add_zero _).symm (zero_add _).symm
  have : b ∈ S := by
    rw [e]
    exact S.add_mem (hinf _) (hf _)
  exact this g

private theorem main (hD : DecE) (hR : RedE) (hV : VolE) (hIv : InvE) (N : MeasE E) (P : CuspSub E 2) {φ : Sm E 2} (hφ : φ ∈ P.V)
    (y : GL (Fin 2) (A E)) : ∫ h in N.D, φ.1 (gl h * y) ∂N.μ = 0 := by
  have hfin := hV E N
  have hL : ∀ φ ∈ P.V, Pp.Lf φ.1 := fun φ hφ => (hD E P φ hφ).1
  have hI : ∀ φ ∈ P.V, ∀ y, IntegrableOn (fun h : G1 E => φ.1 (gl h * y)) N.D N.μ := fun φ hφ y => by
    obtain ⟨B, hB⟩ := bdd hD hR P hφ (isCompact_singleton (x := y))
    exact integ N hfin ((hL φ hφ).1.comp (continuous_gl.mul continuous_const)) fun h => hB h y rfl
  rcases P.irred (Ker N P hI) (fun φ h => h.1) (ker_stable hD hR N hfin P hI) with hK | hK
  · have hz : φ = 0 := by
      refine Subtype.ext (funext fun g => ?_)
      have h1 := (hD E P φ hφ).2.1 g
      simp only [left_inv (hL φ hφ) (fun k hk g => fixed hIv N P hI hL hK hφ k hk g)] at h1
      simpa [Measure.real, adeleMeasure_fundamentalSet] using h1
    rw [hz]
    simp
  · have : φ ∈ Ker N P hI := hK ▸ hφ
    exact this.2 y

end UpperTheory.ConvolutionTheory.RankTwoDescent.MZ

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.meanZero :
    DecE → MeanZero := by
  intro hD E _ _ _ _ _ _ N P φ hφ y
  exact MZ.main hD redE volE invE N P hφ y
