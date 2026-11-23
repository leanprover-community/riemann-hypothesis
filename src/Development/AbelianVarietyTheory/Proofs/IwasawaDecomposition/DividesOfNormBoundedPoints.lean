module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
public import Mathlib.Algebra.MvPolynomial.Cardinal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.HTLine.Dvd

attribute [local instance] Over.cartesianMonoidalCategory

section Algebra

variable {R : Type} [CommRing R]

theorem mk_le_of_finiteType {D : Type} [CommRing D] (σ : D →+* R) (hσ : σ.FiniteType)
    (h : Cardinal.mk D ≤ Cardinal.continuum) : Cardinal.mk R ≤ Cardinal.continuum := by
  letI := σ.toAlgebra
  have : Algebra.FiniteType D R := hσ
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 this
  refine (Cardinal.mk_le_of_surjective hf).trans (MvPolynomial.cardinalMk_le_max.trans ?_)
  exact max_le (max_le h ((Cardinal.lt_aleph0_of_finite _).le.trans Cardinal.aleph0_le_continuum)) Cardinal.aleph0_le_continuum

end Algebra

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem mem_opn (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) {x : Z.X} (hx : ∀ x' : Z.X, x' ⤳ x → x' = x) :
    x ∈ Z.opn := by
  have := GlobalTheory.ProjBlowup.isDiscreteValuationRing_coeff Z.i.c hp.ne_zero hW
  have hN : GlobalTheory.IsNormalScheme Z.X := Z.normal
  have := isProper_str (Z.i.c.V W) Z.n
  have : LocallyOfFiniteType Z.toPre.s := by
    unfold Pre.s
    infer_instance
  have : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.toPre.s
  have hc := irreducibleComponent_mem_irreducibleComponents x
  have ho := GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents hc
  have hg := hc.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hc)
  have e := hx _ (hg.specializes mem_irreducibleComponent)
  rw [e] at hg
  obtain ⟨y, hy, hyo⟩ := Z.dense.inter_open_nonempty _ ho ⟨_, mem_irreducibleComponent⟩
  have hopen : IsOpen Z.opn := Z.cover ▸ isOpen_iUnion fun a => (Z.U a).1.isOpen
  exact (hg.specializes hy).mem_open hopen hyo

theorem exists_base (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) {U : Z.X.Opens} (hU : IsAffineOpen U) :
    ∃ σ : Z.i.c.V W →+* Γ(Z.X, U), σ.Flat ∧ σ.FiniteType := by
  have := GlobalTheory.ProjBlowup.isDiscreteValuationRing_coeff Z.i.c hp.ne_zero hW
  have := isProper_str (Z.i.c.V W) Z.n
  have : LocallyOfFiniteType Z.toPre.s := by
    unfold Pre.s
    infer_instance
  have := Z.flat
  let σ : Z.i.c.V W →+* Γ(Z.X, U) := (Spec.preimage (hU.fromSpec ≫ Z.toPre.s)).hom
  have e : spMap σ = hU.fromSpec ≫ Z.toPre.s := Spec.map_preimage _
  have h1 : Flat (spMap σ) := by rw [e]; infer_instance
  have h2 : LocallyOfFiniteType (spMap σ) := by rw [e]; infer_instance
  exact ⟨σ, (HasRingHomProperty.Spec_iff (P := @Flat)).1 h1, (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h2⟩


end Model

end GlobalTheory.HTLine.Dvd
