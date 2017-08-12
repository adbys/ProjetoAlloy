module imobiliaria

sig Apartamento {
	quartos: set Quarto
}
sig Quarto {}

fact fato {
	all a: Apartamento | some a.quartos
	some a:Apartamento | some a.quartos
	all q: Quarto, a:Apartamento, a1:Apartamento | q in a.quartos and q in a1.quartos => a = a1
	all q: Quarto |  one q.~quartos 
}
pred temQuartos[a:Apartamento] {
	some a.quartos
}

fact {
	all a: Apartamento | temQuartos[a]
}

pred show[]{}
run show

