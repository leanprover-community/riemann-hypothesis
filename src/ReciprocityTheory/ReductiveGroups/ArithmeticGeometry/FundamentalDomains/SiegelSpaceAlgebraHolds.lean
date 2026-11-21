import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivityHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CoefficientConvolutionOfSubCoefficients
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SublatticeCoefficients

section
namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem coefficientConvolution_holds : CoefficientConvolution (E := E) :=
  PeriodLatticeMembership.coefficientConvolution_of_subCoefficients (fun r X la P hP ξ hξ x hx ω hωp hωi k ν hk =>
    SublatticeCoefficients.subCoeff X la P hP ξ hξ x hx ω hωp hωi k ν hk)

end ReciprocityTheory.ChartRestriction.G.FD
end

section
namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem siegelSpaceAlgebra_holds : SiegelSpaceAlgebra (E := E) := BoundedSectionAlgebra.siegelSpaceAlgebra_of moderateCoefficientPositivity_holds coefficientConvolution_holds

end ReciprocityTheory.ChartRestriction.G.FD
end
