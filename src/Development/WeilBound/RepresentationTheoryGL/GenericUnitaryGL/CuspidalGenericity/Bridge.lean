import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNontrivialDerivative
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalIsGeneric

section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

theorem GlobalTheory.BZSeg.Cusp.isGenericFor_of_isCuspidal_direct :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin (N + 1)) k) V), IsCuspidal π → Nontrivial V → IsGenericFor ψ π :=
  GlobalTheory.CompanionTheory.BZDeriv.isGenericFor_of_isCuspidal_of GlobalTheory.CompanionTheory.BZMirDer.NonZero.exists_derivative_nontrivial
    (fun k _ _ _ _ ψ m n V _ _ π => GlobalTheory.CompanionTheory.BZMirDer.twKer_resM_derUnipM (k := k) ψ m n V π) GlobalTheory.T.cuspidal_twisted_kernel_top
    (fun k _ _ _ _ ψ N V _ _ π => GlobalTheory.CompanionTheory.DerWhit.twKer_derUnip_zero (k := k) ψ N V π)
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace GlobalTheory.BZSeg.Cusp

theorem nontrivial_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  exact bot_ne_top (α := Subrepresentation ρ) (Subrepresentation.ext (Subsingleton.elim _ _))

theorem cuspGeneric (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    GlobalTheory.BZSeg.CuspGeneric k := by
  intro N V _ _ π hN _ hirr hc
  obtain ⟨ψ, hψc, hψ1⟩ := exists_continuous_addChar_ne_one k
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  exact ⟨ψ, hψc, hψ1, GlobalTheory.BZSeg.Cusp.isGenericFor_of_isCuspidal_direct k ψ hψc hψ1 M V π hc (nontrivial_of_isIrreducible π hirr)⟩

end GlobalTheory.BZSeg.Cusp

end
end
