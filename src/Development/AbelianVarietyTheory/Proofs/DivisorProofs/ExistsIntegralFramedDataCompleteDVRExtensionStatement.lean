module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralFramedDataCompleteDVRExtension
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
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels

theorem _root_.GlobalTheory.T.exists_integralFramedData_completeDVR_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (T T' : CDVR) (iT : T.Fr →+* T'.Fr) (φ : T.V →+* T'.V), (∀ a : T.V, algebraMap T'.V T'.Fr (φ a) = iT (algebraMap T.V T.Fr a)) → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)), SABMap t' G (spMap (algebraMap T.V T.Fr)) → ∀ (n : ℕ) (w : Fin n → (epsR T.V ⟶ G.G)), IsLieBasis w → ∀ (θ : G.PP.L.Sec), Generates (X := G.G) θ → ∀ (k : KeyIn T.Fr), IsFibreOf k G.G G.PP.L G.PP.rig θ w (algebraMap T.V T.Fr) → ∃ (G' : SAB H (Sp T'.V)) (t'' : SAB H (Sp T'.Fr)) (_ : SABMap t'' t' (spMap iT)) (_ : SABMap t'' G' (spMap (algebraMap T'.V T'.Fr))) (n' : ℕ) (w' : Fin n' → (epsR T'.V ⟶ G'.G)) (θ' : G'.PP.L.Sec) (k' : KeyIn T'.Fr), IsLieBasis w' ∧ Generates (X := G'.G) θ' ∧ IsFibreOf k' G'.G G'.PP.L G'.PP.rig θ' w' (algebraMap T'.V T'.Fr) ∧ KeyPB k' k iT := by
  first | exact @GlobalTheory.FramedExt.exists_framed_ext | exact GlobalTheory.FramedExt.exists_framed_ext | (intros; apply GlobalTheory.FramedExt.exists_framed_ext <;> assumption)
