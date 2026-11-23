module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.Points

namespace GlobalTheory.FlagEmb.QuotLine

section Pull

variable {X Z : Scheme.{0}} (f : Z ⟶ X) (L : LB X)

variable {f L} {W V : Z.Opens} {i j k : L.ι}

end Pull

section Three

variable {X X₀ X₁ Z : Scheme.{0}} (f : Z ⟶ X) (f₀ : Z ⟶ X₀) (f₁ : Z ⟶ X₁) (L : LB X) (L₀ : LB X₀) (L₁ : LB X₁)
  {I : Type} (a : I → L.ι) (b : I → L₀.ι) (c : I → L₁.ι)

variable {f f₀ f₁ L L₀ L₁ a b c}

end Three

section Val

variable {Z : Scheme.{0}} {U W : Z.Opens} (hU : IsAffineOpen U)

theorem valR_chart {C : Type} [CommRing C] (φ : Γ(Z, U) →+* C) (s : Γ(Z, U)) : valR (spMap φ ≫ hU.fromSpec) U s = φ s := by
  have h := le_preimage_specMap_fromSpec hU (CommRingCat.ofHom φ)
  exact (valR_eq _ U h s).trans (congrArg (fun t => t.hom s) (valMap_specMap_fromSpec hU (CommRingCat.ofHom φ) h))

end Val

end GlobalTheory.FlagEmb.QuotLine
