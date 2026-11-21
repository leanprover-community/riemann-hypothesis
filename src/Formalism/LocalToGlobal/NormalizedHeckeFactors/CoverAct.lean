import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain Module Module.End

namespace Formalism.L2.NCov

variable {O K V : Type*} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] {S : Set (End K V)} [IsLocalRing O]




end Formalism.L2.NCov

namespace Formalism.L2

variable {D : D7} {M : MtFam D}

def SplitEx (D : D7) : Prop :=
  ∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ

theorem hecke_transport {μ μ' : D.what₂.Tup} {j j' : ℕ} (hμ : μ = μ') (hj : j = j')
    (a1 : 1 ≤ j) (a2 : j ≤ D.R.m) (b1 : 1 ≤ j') (b2 : j' ≤ D.R.m)
    (e : D.what₂.MtL μ j = D.what₂.MtL μ' j') (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ) (x x' : D.what₂.MtL μ j) :
    (M μ' j' b1 b2).real (D.what₂.jMt μ' j' (cast e x')) =
        NG.tN (M μ' j' b1 b2).J s ϖ k ((M μ' j' b1 b2).real (D.what₂.jMt μ' j' (cast e x))) ↔
      (M μ j a1 a2).real (D.what₂.jMt μ j x') =
        NG.tN (M μ j a1 a2).J s ϖ k ((M μ j a1 a2).real (D.what₂.jMt μ j x)) := by
  subst hμ hj
  simp only [cast_eq]



def etaN (T : NormalizedLocalCompatibility D M) (j : ℕ) (w : D.what₂.places.Pl) : ℚ := etaC T.B j w (goodPts T j w)


end Formalism.L2
