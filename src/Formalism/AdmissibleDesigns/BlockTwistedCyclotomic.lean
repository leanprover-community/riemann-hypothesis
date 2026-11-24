module

public import Formalism.AdmissibleDesigns.InertiaActsTrivially
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.ShaT

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K
open Formalism.MainNotions.N.K.QS Formalism.RepresentationBoundsCohomology.FIN
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Gen

variable {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]

def selRep2 (ρ : Representation R G M) {V VS : Type} (J : V → Subgroup G) (JS : VS → Subgroup G)
    (D : ℕ → Subgroup G) (F : ∀ w, Submodule R (H1z (resRep ρ (D w)))) (P : Finset ℕ) : Submodule R (H1z ρ) :=
  (lcH1 ρ ⊓ (⨅ v, unrH1 ρ (J v)) ⊓ ⨅ v, unrH1 ρ (JS v)) ⊓ ⨅ w ∈ P, (F w).comap (resH1 ρ (D w))

def Fsha (ρ : Representation R G M) (D : ℕ → Subgroup G) (Iq : ∀ w, Subgroup (D w)) (qs : Finset ℕ) (w : ℕ) :
    Submodule R (H1z (resRep ρ (D w))) :=
  if w ∈ qs then unrH1 (resRep ρ (D w)) (Iq w) else ⊥

def RepIso {M' : Type} [AddCommGroup M'] [Module R M'] (ρ : Representation R G M) (ρ' : Representation R G M') :
    Prop :=
  ∃ φ : M ≃ₗ[R] M', ∀ g m, φ (ρ g m) = ρ' g (φ m)

end Gen

def CoefChange (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] (ψ : G →* ℤ_[l]ˣ) {V VS : Type} (J : V → Subgroup G)
    (JS : VS → Subgroup G) (D : ℕ → Subgroup G) (Iq : ∀ w, Subgroup (D w)) (qs P : Finset ℕ),
    let ψO : G →* Oˣ := (Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp ψ
    let ρO := Formalism.GaloisCohomology.scalRep (KO O) ψO
    let ρZ := Formalism.GaloisCohomology.scalRep (Formalism.GaloisCohomology.QZ l) ψ
    Module.length O ↥(selRep2 ρO J JS D (Fsha ρO D Iq qs) P) ≤
      Module.length O (O ⧸ Ideal.span {((l : ℕ) : O)}) * Module.length ℤ_[l] ↥(selRep2 ρZ J JS D (Fsha ρZ D Iq qs) P)

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

def Pall : Finset ℕ := rowsN i dc ∪ qsN i dc ∪ univ.image (colIdx i dc)

def cycE : GE D.nd →* ℤ_[D.nd.l i]ˣ := cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i)

def qzE (e : ℕ) : Representation ℤ_[D.nd.l i] (GE D.nd) (Formalism.GaloisCohomology.QZ (D.nd.l i)) :=
  Formalism.GaloisCohomology.scalRep (Formalism.GaloisCohomology.QZ (D.nd.l i)) (cycE i ^ (-(e : ℤ)))

def koE (e : ℕ) : Representation (D.nd.O i) (GE D.nd) (KO (D.nd.O i)) :=
  Formalism.GaloisCohomology.scalRep (KO (D.nd.O i)) ((Units.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i)).toMonoidHom).comp
    (cycE i ^ (-(e : ℤ))))

def selZ (e : ℕ) : Submodule ℤ_[D.nd.l i] (H1z (qzE i e)) :=
  selRep2 (qzE i e) (Io i) (IS i) (decs D.host.E (Aw i dc)) (Fsha (qzE i e) (decs D.host.E (Aw i dc)) (I i dc) (qsN i dc))
    (Pall i dc)

def BlockTwistedCyclotomic (c : Fin (D.R.t + 1)) : Prop :=
  RepIso (uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ) (koE i ((c : ℕ) - 1))

def ZlSha (e : ℕ) : Prop :=
  Module.length ℤ_[D.nd.l i] ↥(selZ i dc e) ≤ Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ)

end Rec

end Formalism.MainNotions.N.K.ShaT

end
