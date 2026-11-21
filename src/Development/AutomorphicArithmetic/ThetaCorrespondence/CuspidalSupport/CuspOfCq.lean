import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.LocalGlobalOfIwahori
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PstAndWdAtOfIsRegAlg
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.GaloisStatementWeakOfFull

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N
open GlobalTheory GlobalTheory.GalOfCusp GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst

namespace UpperTheory.Lit.Car

section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

structure CQ (x y : WD h) : Prop where
  dim : x.lpDim = y.lpDim
  mono : y.mono0 → x.mono0
  ine : (∀ g : ↥(Weil h), (g : G E Ω) ∈ ⁅Ine (F := E) A, Ine (F := E) A⁆ → LocalGlobalAboveLAlt.Triv y g) →
    ∀ g : ↥(Weil h), deg g = 0 → x.charPol g = y.charPol g
  temp : Odd y.lpDim → ∀ s : ℝ, (y.lpTw s).tempered → (x.lpTw s).tempered

theorem CQ.of_eq {x y : WD h} (e : x = y) : CQ x y := by
  subst e; exact ⟨rfl, id, fun _ _ _ => rfl, fun _ _ h => h⟩
end

def LG : Prop := LocalGlobalAboveLAlt.Glob fun x y => CQ x y

theorem lgG (H : GlobalTheory.GalOfCusp.LocalGlobalAboveL) : LG :=
  fun E Ω _ _ _ _ _ _ l _ ι a ha π hc hr r wt HT hG P AI hT w hw A h O _ _ _ Bw hj σ hσ rc hrc =>
    CQ.of_eq (H E Ω l ι a ha π hc hr r wt HT hG P AI hT w hw A h O Bw hj σ hσ rc hrc)




theorem weak {D : D7} (h : Formalism.MainNotions.SumRepresentations.adm2 D) : GaloisRepresentationsWeak D.nd D.naut := galois_statement_weak_of_full _ _ h
theorem weak' {D : D7} (h : GaloisRepresentationsWeak D.nd D.naut) : GaloisRepresentationsWeak D.nd D.naut := h
theorem weakA {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
    (h : Formalism.MainNotions.SumRepresentations.At.exists_galois_rep_local_global_compatible N A) : GaloisRepresentationsWeak N A := galois_statement_weak_of_full _ _ h
theorem weakA' {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
    (h : GaloisRepresentationsWeak N A) : GaloisRepresentationsWeak N A := h


end UpperTheory.Lit.Car
