module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeterminantIdealCharacterClassLatticeEq
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.determinantIdealCharacter_classLattice_eq : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => (∀ (N : ℕ) (M M' : SDLat D.host.E N), ∀ g ∈ Formalism.L2.Herm.UstdAf D.sp.cm N, Formalism.L2.Herm.Carries g M.1 M'.1 → ∀ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Formalism.L2.Herm.IsDetOf D.sp.cm y g → D.relDet N M M' = QuotientGroup.mk (dtU y)) → (∀ i hi β, latCo D.sp (gramN D i hi) (A.crd i hi) a 1 ((St i hi).K β).lev.Lb = StandardLatticesGL3.stdL D (D.R.N i)) → ∀ i (hi : i ≤ D.R.m) c, t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (t.seam.lat ((t.rd u μ).N i c))) = ((D.chiD ((t.O u μ).dt i c) : ℂˣ) : ℂ)) := by
  first | exact @GlobalTheory.TwV.chi_detId_lat | exact GlobalTheory.TwV.chi_detId_lat | (intros; apply GlobalTheory.TwV.chi_detId_lat <;> assumption)
