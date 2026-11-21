import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.LamLevel
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NormEmbeddingHostFormConstantEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AlgebraicLawsModuliSchemeGoodLevel
import Formalism.LocalToGlobal.Divisibility.FramesLemmas

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.abelian₂.LamModel

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.NormVectorIdentities.Items Formalism.L2.DIV
open scoped Matrix ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_basis {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r} {V : HSp D}
    {dict : ∀ σ : c.F →+* ℂ, GA D V → Σ k, Frame ((U σ).X k).Ψ D.R.r} (h : LevelLaws U V dict)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hd : Dom a n) :
    ∃ N : ℕ, Nonempty (Module.Basis (Fin N) c.F (cusp Xo c U a n)) := by
  have h0 : GoodEmb c (goodOf c c.F.val.toRingHom) := goodEmb_goodOf c _
  have hF : CuspFD Xo c U := (Formalism.L2.PjFree.cuspFD_ofPj U).1
    (GlobalTheory.cuspForms_finiteDimensional_of_isUnf GlobalTheory.firstFiveLaws.1.secBaseChange _ H Dw l Xo c _
      (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) _ h0 ((Formalism.L2.PjFree.isUnf_ofPj (U _)).2 (h.unf _ h0)))
  haveI := hF a n hd
  haveI : Module.Free c.F (cusp Xo c U a n) := Module.Free.of_divisionRing _ _
  exact ⟨_, ⟨Module.finBasis c.F _⟩⟩

theorem hyps_inhabited (D : D7) (hf : 16 ≤ D.R.f) (j : ℕ) (hj : 1 ≤ j ∧ j ≤ D.R.m)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hd : Dom a n) :
    ∃ (l : Level (hostOfRecord D)) (Xo : Moduli (datumW D j hj) l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r)
      (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (S L : ℝ) (N : ℕ),
      LevelLaws U (D.sp.W j) dict ∧ SizeRows D l.M S L ∧
        (absA (datumW D j hj) a : ℝ) + D.R.f * D.R.r * n ≤ S ∧
        Nonempty (Module.Basis (Fin N) c.F (cusp Xo c U a n)) := by
  obtain ⟨l₀, -⟩ := GlobalTheory.Member.Inhab.exists_ctx_ok_at_lift D j hj
  let l : Level (hostOfRecord D) := { l₀ with A := 1, A_pos := one_pos }
  obtain ⟨-, Xo, c, U, dict, h⟩ := LevelModel.exists_levelLaws_at_lift D j hj l rfl
  have h0 : (0 : ℝ) ≤ (absA (datumW D j hj) a : ℝ) + D.R.f * D.R.r * n := by positivity
  obtain ⟨L, hL⟩ := LevelModel.exists_sizeRows D l.M ((absA (datumW D j hj) a : ℝ) + D.R.f * D.R.r * n + 1) hf
    (by linarith)
  obtain ⟨N, hN⟩ := exists_basis h a n hd
  exact ⟨l, Xo, c, U, dict, _, L, N, h, hL, by linarith, hN⟩





end GlobalTheory.CompanionTheory.Ar.abelian₂.LamModel
