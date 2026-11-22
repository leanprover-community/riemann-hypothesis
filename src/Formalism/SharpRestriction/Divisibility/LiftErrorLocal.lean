module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataNChoice
public import Formalism.LocalRingCardinality.DataErr
public import Formalism.LocalRingCardinality.DataKap
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
public import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Formalism.SharpRestriction.LevelLetterCocycles.LocsCoverTw

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.LiftErrorLocal

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped TensorProduct

abbrev Pl (D : D7) : Type := D.what₂.places.Pl

def Over (D : D7) (i : Fin 2) (w : Pl D) : Prop := D.what₂.places.resChar w = D.host.g i

instance instFactG (D : D7) (i : Fin 2) : Fact (D.host.g i).Prime := ⟨D.host.g_prime i⟩

def vG (D : D7) (w : Pl D) (x : D.what₂.LL) : ℝ :=
  (vAdd (D.plEq w) x : ℝ) / (D.what₂.places.ramIdx w : ℝ)

def lifts (D : D7) : Finset ℕ := Finset.Icc 1 D.R.m

attribute [instance] GeoX.ltFin

namespace GeoX

variable {D : D7} {r j p : ℕ} {Lc : ModuliIntegralCharts.Loc D r j p} (G : GeoX Lc)

end GeoX

section Lat

variable (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool)

variable {D i j b}

end Lat

namespace Loc

variable {D : D7} {nch : NChoice D} (X : Loc D nch)

end Loc

section admitted

variable (D : D7) (L : SizeData₂ D) {nch : NChoice D} (X : Loc D nch)

end admitted

section Conclusion₂

variable (D : D7) (L : SizeData₂ D) (EX : ErrX D) {nch : NChoice D} (X : Loc D nch)

def errC : ℝ :=
  (D.R.f : ℝ) * ((D.R.m : ℝ) * (D.R.N D.R.m : ℝ) * ((D.R.N D.R.m : ℝ) + D.R.t) + (D.R.m : ℝ) ^ 3 * L.etaSz)

def Dpi (u : D.what₂.Word) (j : ℕ) : ℝ := ∑ τ : D.what₂.Tau, nuAbs D u j τ

end Conclusion₂

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
  (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.ex x hx i).nch)

end Fam

end Formalism.MainNotions.LiftErrorLocal

end
