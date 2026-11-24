module

public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.UniformizationSplitFormalGroupLawEquivariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.uniformization_split_formal_group_law_equivariant : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegData R I) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D A G) [IsAdicComplete I R] (d g : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (x : Fam G d) (xB : Fam D.toPre.P.A g), NilChart G F.F x → NilChart D.toPre.P.A FB.F xB → ∃ (r : ℕ) (J : Fin d → PS R 1 r) (Q : Fin g → PS R 1 d), ExtSer F.F FB.F J Q ∧ ∀ (OE : Type) [CommRing OE] [StarRing OE] [Module OE D.toPre.X] (io : Out.RingAct G OE) (oD : D.OAct OE) (oA : A.OAct OE), U.OLinear OE oD oA io → ∀ (α : OE → Fin d → PS R 1 d) (αB : OE → Fin g → PS R 1 g), (∀ a, Reads x x (io.act a) (α a)) → (∀ a, Reads xB xB (oD.onB.act a) (αB a)) → ∃ N : OE →+* Matrix (Fin r) (Fin r) ℤ, ∀ a, lin Q * lin (α a) = lin (αB a) * lin Q ∧ lin (α a) * lin J = lin J * (N a).map (Int.castRingHom R) := by
  first | exact @GlobalTheory.unif_extSer_equivariant | exact GlobalTheory.unif_extSer_equivariant | (intros; apply GlobalTheory.unif_extSer_equivariant <;> assumption)
