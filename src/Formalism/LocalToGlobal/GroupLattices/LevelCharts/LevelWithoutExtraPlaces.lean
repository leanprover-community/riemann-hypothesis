module

public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.LevelsOfChChartsCover
public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.AtGLev
public import Formalism.LocalToGlobal.GroupLattices.CloudFilling.CloudBound
public import Formalism.LocalToGlobal.HermitianColumns.HermCols
public import Formalism.LocalToGlobal.HermitianColumns.TiedQC

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits
open scoped TensorProduct

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
  {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

end Generic

section Record

variable {p : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem rank_step (D : D7) (i : ℕ) (hi : i < D.R.m) :
    D.R.k - 1 + (i + 1) * (D.R.t + 1) + 1 = (D.sp.X (i + 1)).rank := by
  rw [D.sp.X_rank (i + 1) hi]
  have := k_pred D.R
  simp only [Ranks.N]
  omega

end Record

end Formalism.L2.G
