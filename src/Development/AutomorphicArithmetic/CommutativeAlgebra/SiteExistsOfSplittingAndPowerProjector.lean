module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverCompFiniteStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev
open UpperTheory.Gal.Int.Geo

theorem UpperTheory.site_exists_of_splitting_and_power_projector :
    MIn → SplitQ → BaseEx → PowProj → SiteEx := by
  intro hM hS hB hP
  intro p _ D G hSc E _ _ e gb hstd w q _ r 𝔴 𝔫 hpl hat hlev
  have sp := hS p D hSc.m1 q
  obtain ⟨N₀, 𝔞, h3, hcq, hcp, hsup, hupow, hlv⟩ := hlev
  obtain ⟨f, b, hmat, hstdb, hqmem, hnorm⟩ :=
    hB q (datAt hat sp) hSc.a1 hSc.m1 E e gb hstd w 𝔴 r hpl hat.le N₀ h3 hcq
  obtain ⟨M⟩ := hM.ex q (datAt hat sp) (Ow w) b N₀ h3 hcq
  have hEt : UpperTheory.Gal.FiniteEtaleModels.IsEtIdeal b 𝔞 :=
    (hM.placeOf q (datAt hat sp) (Ow w) b r 𝔴 hat.max hstdb.pmem hSc.a1 hstdb.ule hstdb.tw 𝔞 hsup).2 hupow
  obtain ⟨Y, π, ρ, hov, ⟨hmπ⟩, hgal⟩ := hM.finModel q (datAt hat sp) (Ow w) b N₀ h3 hcq 𝔞 1 hEt M
  have hfin : IsFinite π := hgal.fin
  have het : Etale π := hgal.etale
  have hMproj : IsProjOver M.s := hM.proj q (datAt hat sp) (Ow w) b N₀ h3 hcq hSc.cpt M
  have hYproj : IsProjOver Y.s := by
    rw [← hov]
    exact GlobalTheory.T.isProjOver_comp_finite (Ow w) M.X Y.X π M.s hfin hMproj
  have hYsm : SmoothOfRelativeDimension (0 + (datAt hat sp).a * ((datAt hat sp).n - 1)) Y.s := by
    rw [← hov]
    haveI : SmoothOfRelativeDimension 0 π := by
      rw [← AlgebraicGeometry.Etale.eq_smoothOfRelativeDimension_zero]
      exact het
    haveI := M.smooth
    infer_instance
  have hPw := fun k => hP q (datAt hat sp) (Ow w) b N₀ h3 hcq Y.X Y.s Y.univ k
  exact ⟨⟨hat, sp, f, b, hmat, N₀, 𝔞, hstdb, hqmem, hnorm, hcp, hsup, hupow, hlv, M, Y, π, hov, hmπ,
    hfin, het, fun k => (hPw k).1 hYproj, fun k => (hPw k).2 _ hYsm⟩⟩
