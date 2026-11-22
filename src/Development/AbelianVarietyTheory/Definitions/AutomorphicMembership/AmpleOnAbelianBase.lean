module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.IsChartIff
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.Pad

attribute [local instance] Over.cartesianMonoidalCategory

section Lattices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

instance finiteDual {O : Type} [CommRing O] (I : Ideal O) : Module.Finite O (DualNumber (O ⧸ I)) :=
  inferInstanceAs (Module.Finite O ((O ⧸ I) × (O ⧸ I)))

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]

end Lattices

section Points

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

structure FlagPt (Z : Model Xo c β) (Ω : Type) [Field Ω] : Type where
  fK : c.F →+* Ω
  y : Sp Ω ⟶ gen Z
  y_over : y ≫ genStr Z = spMap fK
  u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber Ω) ⟶ Z.t.G.left)
  tan : ∀ τ i, IsTanAtG Z.t (y ≫ genι Z) (u τ i)
  eig : ∀ τ i (a : 𝓞 E), u τ i ≫ (Z.t.act.act a).left = spMap (epsMul (fK (embF c τ (a : E)))) ≫ u τ i
  basis : ∀ τ w, IsTanAtG Z.t (y ≫ genι Z) w →
    (∀ a : 𝓞 E, w ≫ (Z.t.act.act a).left = spMap (epsMul (fK (embF c τ (a : E)))) ≫ w) →
      ∃! a : Fin (Dw.mult τ) → Ω, IsCombAtG Z.t (y ≫ genι Z) (u τ) a w

variable {Z : Model Xo c β} {Ω : Type} [Field Ω] (y : FlagPt Z Ω) {C : Type} [NontriviallyNormedField C]
  [IsUltrametricDist C] (io : Ω →+* C)

end Points

section Degrees

variable {A : Type}

end Degrees

namespace ArIn

variable {Tau : Type} [Fintype Tau] {N g : ℕ} {Comp : Type} [Fintype Comp] (I : ArIn Tau N g Comp)

end ArIn

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ)

instance compNe : Nonempty s.Comp := (s.unf κ.σ₀ rfl).2.1

def JcPin (D : D7) (p : ℕ) [Fact p.Prime] (la : PlL D p) (jc : DV.KW p →+* ℂ) : Prop :=
  ∃ W : ValuationSubring ℂ, (∀ x : D.what₂.LL, D.what₂.embLL x ∈ W ↔ la.1.valuation D.what₂.LL x ≤ 1) ∧
    ∀ a : DV.KW p, jc a ∈ W ↔ a ∈ (algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p)).range

section OfPkg

variable {Comp : Type} {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg}
  (P : PadPkg D N j Comp jC ng)

end OfPkg

section Unfold

variable {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg} (L : LocSt D N j ng)
  (G : GlobSt fun p => (L.loc p).Mdl) (M : AdmSt D N j jC) (F : FlatSt s) (I : ArIn D.what₂.Tau N (D.R.f * N) s.Comp)

end Unfold

end GlobalTheory.ShFam.Pad
