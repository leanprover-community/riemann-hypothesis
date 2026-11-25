module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DominatesLiftUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHom
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrNormPush, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrNormPush =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrNormPush", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers\nimport Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap\nimport Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair\nimport Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt\npublic import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LieMet MonObj

namespace GlobalTheory.ShFam.Pad.Pull

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

section Tan

variable {k : Type} [Field k] (x : Sp k ⟶ X) {m : ℕ}

def Ind (u : Fin m → (Sp (DualNumber k) ⟶ t.G.left)) : Prop :=
  (∀ i, IsTanAtG t x (u i)) ∧ ∀ cf cf' w, IsCombAtG t x u cf w → IsCombAtG t x u cf' w → cf = cf'

def Tri (u u' : Fin m → (Sp (DualNumber k) ⟶ t.G.left)) : Prop :=
  ∀ j, ∃ cf : Fin m → k, (∀ i, j < i → cf i = 0) ∧ IsCombAtG t x u cf (u' j)

variable {t x} {u u' u'' : Fin m → (Sp (DualNumber k) ⟶ t.G.left)}

end Tan

section Norm

variable {t} {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] {x : Sp C ⟶ X} {m : ℕ}
  {u u' : Fin m → (Sp (DualNumber C) ⟶ t.G.left)}

end Norm

end GlobalTheory.ShFam.Pad.Pull
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrNormPush =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrNormPush\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag\npublic import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DominatesLiftUnique\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHom\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers\nimport Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap\nimport Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair\nimport Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
open GlobalTheory.LieMet MonObj

namespace GlobalTheory.ShFam.Pad.Pull

attribute [local instance] Over.cartesianMonoidalCategory

section Val

variable {F : Type} [Field F] {X Y : Scheme.{0}}

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Frames

variable {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {l l' : Level H} {c : Coeff l} {c' : Coeff l'}

theorem eig_iff {R : Type} [CommRing R] {x : Sp R ⟶ X} (v : TanM x t.G) (a : 𝓞 E) (s : R) :
    (tv v).left ≫ (t.act.act a).left = spMap (epsMul s) ≫ (tv v).left ↔ actR t.act a v = s • v :=
  ⟨fun h => tan_ext h, fun h => congrArg (fun z => (tv z).left) h⟩

variable {g : X' ⟶ X} (mu : SABMap t' t g) {R : Type} [CommRing R] {x' : Sp R ⟶ X'} {x : Sp R ⟶ X} (hx : x' ≫ g = x)

include hx

end Frames

section Steps

variable {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {l : Level H} {c : Coeff l} {p : ℕ}

end Steps

section Models

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

variable {Z Z' : Mdl Y i₀} {f : Z'.X ⟶ Z.X} (hf : IsMap Z' Z f) {τ : (Y Z'.i).X ⟶ (Y Z.i).X}
  {mu : SABMap (Y Z'.i).t (Y Z.i).t τ} (hT : IsTrans Z.i Z'.i τ mu)

include hf hT

end Models

section Bundle

variable {X Y : Scheme.{0}} (f : Y ⟶ X)

end Bundle

section Main

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z Z' : Mdl Y i₀} {f : Z'.X ⟶ Z.X} {τ : (Y Z'.i).X ⟶ (Y Z.i).X}
  {b : Bool} {st : ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Letter Dw}

variable (hf : IsMap Z' Z f) {mu : SABMap (Y Z'.i).t (Y Z.i).t τ} (hT : IsTrans Z.i Z'.i τ mu)
  (hty : ∀ τ n, n ≤ Dw.mult τ → n ∈ Z.ty τ) (M : LineModel Z b st x)

include hf hT hty

end Main

end GlobalTheory.ShFam.Pad.Pull
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap =====
