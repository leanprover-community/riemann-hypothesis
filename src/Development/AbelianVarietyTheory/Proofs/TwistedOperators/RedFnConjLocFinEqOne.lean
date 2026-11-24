module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.PlaceAwayRed

theorem redFn_conj_locFin_eq_one : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (a : GfC V) (v : HeightOneSpectrum (𝓞 D.host.F)) (PP : Pl D.host.E), (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v → ∀ k : Gv V v, finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∈ St β → redFn β PP (finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V)) = 1 := by
  intro D V β a v PP hPP k hS
  refine GlobalTheory.FinZeta.LevelOff.redFn_eq_one_of_proj β {(_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)} hS (fun u hu => ?_) (Finset.mem_singleton_self _)
  rw [Finset.mem_singleton] at hu
  subst hu
  have e : proj D.sp.cm.sig V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) (embV V v k) = 1 := proj_emb_ne _ _ hPP k
  show proj D.sp.cm.sig V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) ((a : GA D V) * (locFin V v k : GA D V) * ((a⁻¹ : GfC V) : GA D V)) = 1
  rw [coe_locFin, MonoidHom.map_mul, MonoidHom.map_mul, e, mul_one, ← MonoidHom.map_mul, ← Subgroup.coe_mul, mul_inv_cancel,
    Subgroup.coe_one, MonoidHom.map_one]

end GlobalTheory.PlaceAwayRed

end
