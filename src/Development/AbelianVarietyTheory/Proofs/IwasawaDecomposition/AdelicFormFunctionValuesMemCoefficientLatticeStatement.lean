module

public import Formalism.LocalToGlobal.IndefiniteReal.BridgeTie
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.FramesExistOfDiagonalTypePlaces
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicFormFunctionValuesMemCoefficientLattice
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.adelicFormFunction_values_mem_coefficientLattice : ∀ (D : D7) (V : HSp D), Seed.FrmC.StdLat V → ∀ (c : CoefA V) (S : CSD D.what₂.LL) (J : Subgroup (Bridge.Gf V)) (χ : J →* ℂˣ) (pres : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL c.coef.ρ J χ) (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) pair del, Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam) → Bridge.CoefTie V c.coef pres lam c0 pair (nabAtr (labLL D) lam) del → (∀ k ∈ J, ∀ h, Bridge.hLat V (h * k) = Bridge.hLat V h) → (∀ k : J, ∃ z : 𝓞 D.what₂.LL, D.what₂.embLL (z : D.what₂.LL) = (χ k : ℂ)) → ∀ f : S.Forms, (∀ h, pres.ext f.1 h ∈ Set.range c0) ∧ ((∀ a, f.1 a ∈ S.Nab a) → ∀ h, ∃ v ∈ nabAtr (labLL D) lam (Bridge.hLat V h), pres.ext f.1 h = c0 v) := by
  first | exact @GlobalTheory.MtIn.ext_vals | exact GlobalTheory.MtIn.ext_vals | (intros; apply GlobalTheory.MtIn.ext_vals <;> assumption)
