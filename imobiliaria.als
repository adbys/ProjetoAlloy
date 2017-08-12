module imobiliaria

sig ListaEspera{
	clientes: set Pessoa
}

sig Apartamento {
	quartos: set Quarto
}
sig Quarto {
	morador: Pessoa
}
sig Pessoa{}

fact fato {
	#ListaEspera = 1
	#Apartamento = 1
	//Todo apartamento tem um conjunto de quartos
	all a: Apartamento | some a.quartos
	//Todo quarto pode ter um morador
	all q: Quarto | some q.morador
//	some a:Apartamento | some a.quartos
    //Todo quarto so esta em 1 apartamento
	all q: Quarto, a:Apartamento, a1:Apartamento | q in a.quartos and q in a1.quartos => a = a1
	//Todo quarto faz parte de um apartamento
	all q: Quarto |  one q.~quartos
	//Toda pessoa so esta em 1 quarto
	all p: Pessoa, q:Quarto, q1:Quarto | p in q.morador and p in q1.morador => q = q1
	all p: Pessoa, l:ListaEspera, q:Quarto | p in l.clientes or p in q.morador 
	all l:ListaEspera, q:Quarto | no(l.clientes + q.morador)
}
pred temQuartos[a:Apartamento] {
	some a.quartos
}

fact {
	all a: Apartamento | temQuartos[a]
}

pred show[]{}
run show

