module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeometricHalfPhaseOneOverLawfulCore
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

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_geometricHalf_phase_one_over_lawful_core : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), VolTieG D → LawsJ T → LawsCore T.toCore → AlgTie T → T.pb = R.C.P.pb → PreChar R → ValKs R → FrameKs T.Q.c.F R.MW → Formalism.L2.Host.ValLL D R.C → Finite T0 → QGuard R → (∀ i, VStd D i) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → ∃ dict mu chiW x₀ cE nW FW, ∃ B : GeoHalf (reCore T dict mu chiW x₀ cE) (updFW R nW FW) (fun _ => 1), B.κ = kapTop D ∧ InGeo B ∧ Fired (reCore T dict mu chiW x₀ cE) (updFW R nW FW) B.κ B.v₀ B.O (fun _ => 1) ∧ (∀ i, OneMapRowR (reCore T dict mu chiW x₀ cE) (updFW R nW FW) B.κ B.v₀ B.O (fun _ => 1) i) ∧ IoExt (updFW R nW FW) ∧ PreChar (updFW R nW FW) ∧ (updFW R nW FW).grp_chiW ∧ (updFW R nW FW).LUnif ∧ (updFW R nW FW).LIntegral ∧ LawsCore (reCore T dict mu chiW x₀ cE).toCore := by
  first | exact @GlobalTheory.GeoHalfTop.exists_geoHalf | exact GlobalTheory.GeoHalfTop.exists_geoHalf | (intros; apply GlobalTheory.GeoHalfTop.exists_geoHalf <;> assumption)
