module

public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableEmbeddingEquiv
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
open Formalism.MainNotions.KudlaSiegelWeil (Restr)

noncomputable section

namespace GlobalTheory.PureDS

open GlobalTheory.AutMult

section Comb

variable {α β ι : Type} {Hs : α ⊕ β → Type} {E : ι → Type}

variable {p : ι → α} {A : ∀ i, E i → Hs (.inl (p i))} {y0 : ∀ v, Hs v} {z : ∀ i, E i}

end Comb

section Abstract

variable {ι G K κ : Type} {Γ Hs : ι → Type} [Fintype ι] [DecidableEq ι] [Group G] [∀ i, Group (Γ i)]
  [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K] [TopologicalSpace G] [∀ i, TopologicalSpace (Γ i)]
  {e : ∀ i, Γ i →* G} {δ : ∀ i, Γ i →* (Hs i →L[ℂ] Hs i)} {ρ : G →* (K →L[ℂ] K)}

end Abstract

section Act

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Hs : Formalism.MainNotions.SchurIrreducible.Pl F → Type} [∀ v, NormedAddCommGroup (Hs v)] [∀ v, InnerProductSpace ℂ (Hs v)]
  {δ : ∀ v, GPl σ J v →* (Hs v →L[ℂ] Hs v)} {ξ : ∀ v, Hs v} {π : GAd σ J →* (H →L[ℂ] H)} {B : (∀ v, Hs v) → H}
  {ι : Type} {Eτ : ι → Type} [∀ i, NormedAddCommGroup (Eτ i)] [∀ i, InnerProductSpace ℂ (Eτ i)]

end Act

end GlobalTheory.PureDS

namespace GlobalTheory.PureDS

open GlobalTheory.AutMult

section Expand

end Expand

section Main

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {π : GA D V →* (H →L[ℂ] H)} {R : ∀ v, IrrU (GPl D.sp.cm.sig V.gram v)}
  {ξ : ∀ v, (R v).H} {B : (∀ v, (R v).H) → H}

end Main

end GlobalTheory.PureDS

