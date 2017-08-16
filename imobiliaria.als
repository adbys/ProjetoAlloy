module imobiliaria

----------------------------Assinaturas----------------------------
one sig ListaEspera{
	clientes: set Pessoa
}

sig Nome {
}

sig Pessoa{
	nome: one Nome
}

sig ClientePreferencial in Pessoa {
}

sig Quarto {
	morador: lone Pessoa
}

sig Suite  {
	moradorSuite: lone Pessoa
}

abstract sig Apartamento {
	quartos: set Quarto,
	suites: set Suite
}

sig Cobertura extends Apartamento {
}

sig ApartamentoPequeno extends Apartamento {
}

sig ApartamentoGrande extends Apartamento {
}

----------------------------Fatos----------------------------

fact fato {
	#Apartamento = 6
	#ApartamentoPequeno = 3
	#ApartamentoGrande = 2
	#Cobertura = 1
	
	-- Todo nome so esta em uma pessoa
	all n:Nome, p:Pessoa, p1:Pessoa | n in p.nome and n in p1.nome => p = p1
	
	--Todo apartamento tem um conjunto de quartos
	all a: ApartamentoPequeno | #quartosDoApartamento[a] = 1  and #suitesDoApartamento[a] = 1
	all a: ApartamentoGrande | #quartosDoApartamento[a] = 1 and #suitesDoApartamento[a] = 2
	all c: Cobertura | #quartosDoApartamento[c] = 0 and #suitesDoApartamento[c] = 3
    
	--Todo quarto so esta em 1 apartamento
	all q: Quarto, a:Apartamento, a1:Apartamento | quartoSoEstaEmUmApt[q,a,a1]

	--Todo quarto faz parte de um apartamento
	all q: Quarto |  one quartosEmConjuntoDeTodosOsQuartos[q]

	all n:Nome | one nomesEmConjuntoDeTodosOsNome[n]

	--Todo quarto faz parte de um apartamento
	all s: Suite |  one suitesEmConjuntoDeTodasAsSuites[s]

	--Toda pessoa so esta em 1 quarto
	all p: Pessoa, q:Quarto, q1:Quarto | todaPessoaEmUmQuarto[p,q,q1]

	--Cliente ou esta em quarto ou na lista de espera 
	all p:Pessoa | clienteEstaEmQuartoOuListaEspera[p]

}

----------------------------Funcoes----------------------------

fun nomesEmConjuntoDeTodosOsNome[n:Nome]: set Pessoa {
	n.~nome
}

fun quartosEmConjuntoDeTodosOsQuartos[q:Quarto]: set Apartamento {
	q.~quartos
}

fun suitesEmConjuntoDeTodasAsSuites[s:Suite]: set Apartamento {
	s.~suites
}


fun suitesDoApartamento[a:Apartamento]: set Suite {
	a.suites
}

fun quartosDoApartamento[a:Apartamento]: set Quarto {
	a.quartos
}

----------------------------Predicados----------------------------

pred clienteEstaEmQuartoOuListaEspera[p:Pessoa] {
	one(p.~morador) and no(p.~clientes) and no(p.~moradorSuite) or (no(p.~morador) and one(p.~clientes) and no(p.~moradorSuite)) or (no(p.~morador) and no(p.~clientes) and one(p.~moradorSuite)) 

}

pred quartoSoEstaEmUmApt[q: Quarto, a:Apartamento, a1:Apartamento] {
	q in a.quartos and q in a1.quartos => a = a1
}

pred todaPessoaEmUmQuarto[p:Pessoa, q:Quarto, q1:Quarto] {
	p in q.morador and p in q1.morador => q = q1
}

----------------------------Asserts----------------------------

assert apartamentosCom2ou3Quartos {
	all a:Apartamento | #(a.quartos) = 2 or #(a.quartos) = 3
}

assert todoQuartoEstaEmUmApt {
	all q: Quarto |  #(q.~quartos) = 1
}

assert todaSuiteEstaEmUmApt {
	all s: Suite |  #(s.~suites) = 1
}


assert todaCoberturaPossui3Suites{
	all c:Cobertura | #(c.quartos) = 0 and #(c.suites) = 3
}

check apartamentosCom2ou3Quartos
check todoQuartoEstaEmUmApt
check todaSuiteEstaEmUmApt
check todaCoberturaPossui3Suites

pred show[]{}
run show for 30

