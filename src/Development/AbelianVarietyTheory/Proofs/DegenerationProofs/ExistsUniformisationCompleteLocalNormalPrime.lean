module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ToATotal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PelSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVGenericFibreOfTripleStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalDomainPrimeStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCubicalBundleOfSymmetricSemiAbelianStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

namespace GlobalTheory.LN.UnifPrime

theorem hypW_of_triple {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S) :
    HypW t.G t.PP.L :=
  ⟨t.act.act H.w0, t.act.act (H.bar H.w0), t.act.hom _, t.act.hom _,
    by rw [← t.act.add, GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel, t.act.one], t.prim, t.adj _⟩

theorem exists_pelUnif : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Ega → USt → PelSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → IsPrincipalIdealRing (R ⧸ I) → ∀ (t : SAB H (Sp R)), PolAt t (jK R) → SplitOver t.G I → ThetaNZ t.G t.PP.L → ∃ P : PELUnif I t, P.TorsionIso := by
  intro h1 h2 h3 _ _ hE hU hP E _ _ _ H R _ _ _ I hA hpi t hpol hs hth
  obtain ⟨A, -, gen, hgen, hL, -⟩ := GlobalTheory.T.exists_polAV_generic_fibre_of_triple h1 h2 E H R t hpol
  have := hA.1.1
  have := hA.2.2.1
  obtain ⟨P, hPL, -⟩ := GlobalTheory.T.exists_cubical_bundle_of_symmetric_semiAbelian h1 R A t.G t.semi gen hgen t.PP t.cub t.sym
  obtain ⟨D, U, hUL, -⟩ := GlobalTheory.T.exists_uniformisation_completeLocalDomain_prime h1 h2 h3 hE hU R I hA hpi t.G P t.semi (hPL ▸ hypW_of_triple t) hs
    (hPL ▸ hth) A gen hgen (hPL ▸ hL)
  obtain ⟨Q, -, -, -, hQ⟩ := hP E H R I hA.1 t D A U (hUL.trans hPL)
  exact ⟨Q, hQ⟩

end GlobalTheory.LN.UnifPrime
