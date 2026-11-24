module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.HodgeKill
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartNzdAlg
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.EtaleSplit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.nzdChart :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) (k : Fin d), (π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom ((B.c α).t k) ∈ nonZeroDivisors Γ(Y, (B.c α).C k) := by
  intro K _ W Z Y q i π D d B α k
  exact UpperTheory.Gal.KunnethLefschetz.G.PX.chartNzdAlg
    (MvPolynomial.eval₂Hom (Pb.strV q (B.V α)) (B.c α).x)
    (π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom
    (B.c α).t ((B.c α).u k) k
    (UpperTheory.Gal.KunnethLefschetz.G.PX.etaleSplit B α) ((B.c α).surj k) ((B.c α).rel k)
