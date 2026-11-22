module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPinsRec
public import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Formalism.LocalRingCardinality.DataKap
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ComplexResidueRing
public import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
public import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HalfGeometricCovers

open Formalism.L2.Pj NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDeterminantRoot
open scoped TensorProduct

section Adeles

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable {F}

end Adeles

section Lattices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
variable {H : Host E} {Dw : Datum H} {r n : ℕ}

def barI (H : Host E) (𝔞 : Ideal (𝓞 E)) : Ideal (𝓞 E) := 𝔞.map (H.bar : 𝓞 E →+* 𝓞 E)

end Lattices

section Record

variable {D : D7}

variable (T : CoreJ D) {X : ThetaX D} (Tt : ThetaTied D X) (j : ℕ)

variable {T} {c' : Coeff T.Q.l} (h : T.Q.c.F ≤ c'.F)

variable (ka : WeightFamilies.Wt D j) (lam : D.what₂.Tau → DomWeight D.R.nV)
  (PQ : D.what₂.Tup → Ideal (𝓞 D.host.E)) (β : Fin D.R.r → (T.Q.Dw j).La)
  (Cl : D.what₂.Tup → Type) [∀ t, Fintype (Cl t)]
  (Lh : ∀ t, Cl t → Submodule (𝓞 D.host.E) (Fin D.R.nV → D.host.E)) (gam : ∀ t, Cl t → ℕ) (vol : D.what₂.Tup → c'.F)
  (thAd : ∀ t, (Cl t → VVc c' lam) → AutQ (T.V j (sig0 T.Q.c)) → ℂ) (Pl : ∀ t, (Cl t → VVc c' lam) → Prop) (ph : ℂ)
  (ξ : D.what₂.Tup → IdF D →* Circle) (bad : D.what₂.Tup → ℕ)
  (d : D.what₂.Tup → DeltaDat (T.Q.Xo j) c' D.R.nV)
  (φ : ∀ t, (Fin D.R.nV → LevQc (T.Q.Dw j) (d t).l₂) → c'.F)
  (w : ∀ t, Cl t → (Fin D.R.nV → LevQ (T.Q.Dw j) (d t).l₂) → c'.F)
  (La : ∀ t, Cl t → GenLat D.host.E D.R.nV) (Nc : ∀ t, Cl t → ℕ) (ep : ∀ t, Cl t → c'.F)
  (io : VVc c' lam →ₗ[c'.F] MvPolynomial (LtN (T.Q.Dw j) D.R.nV) c'.F)

end Record

end GlobalTheory.IndefiniteRowSideFullHecke.HalfGeometricCovers
