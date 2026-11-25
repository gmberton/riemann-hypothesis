module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.WittVector.Teichmuller
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

open scoped NNReal
open Ideal Finset GlobalTheory.Per.AinfComplete

namespace GlobalTheory.WittTeichComplete

open scoped NNReal in
open Ideal Finset in
theorem _root_.GlobalTheory.WittTeichComplete.main : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [CharP O l]
    [PerfectRing O l] (x : O), x ≠ 0 → IsAdicComplete (Ideal.span {x}) O →
    IsAdicComplete (Ideal.span {WittVector.teichmuller l x}) (WittVector l O) ∧
      IsAdicComplete (Ideal.span {((l : ℕ) : WittVector l O)} ⊔
        Ideal.span {WittVector.teichmuller l x}) (WittVector l O) := by
  intro l _ O _ _ _ _ x _ hc
  haveI := hc
  have hcc : WittVector.constantCoeff (WittVector.teichmuller l x) = x := by
    simp [WittVector.constantCoeff]
  have htx : Tails x := tails_of_mod x x fun b =>
    ⟨b, fun n => b (n + 1), fun n => (sub_add_cancel _ _).symm⟩
  obtain ⟨h₁, h₂⟩ := witt_complete (WittVector.teichmuller l x) (hcc ▸ htx)
    (fun r hr => eq_zero_of_haus x r fun n => Ideal.mem_span_singleton.2 (hcc ▸ hr n))
  refine ⟨h₂, ?_⟩
  rwa [Ideal.span_insert] at h₁

end GlobalTheory.WittTeichComplete
