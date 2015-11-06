open util/boolean
open util/integer 

// *** SIGNATURES ***
sig Str{}
sig SInt{v: one Int}
{
v>=0
}
sig Integer{}

sig Location{
	latitude: one Integer,
	longitude: one Integer
}

sig Passenger {
	email: one Str,
	phone: one Str,
	requests: some Request,
}

sig Request{
	ID: one Integer,
	meetingPoint: one Location,
	people: one Int,
	passenger: one Passenger,
	active: one Bool,			
	driver: some TaxiDriver,
	executedAt: one SInt,
	finishedAt: one SInt
} 
{
	people>0
	#driver = div[people,3]
}


sig Reservation {
	ID: one Integer,
	meetingPoint: one Location,
	people: one Int,
	passenger: one Passenger,
	active: one Bool,
	driver: some TaxiDriver,
	executedAt: one SInt,
	finishedAt: lone SInt,
	requestTime: one SInt,
}
{
	requestTime.v<=minus[executedAt.v,2]
	people>0
	#driver = div[people,3]
}

sig TaxiDriver {
	taxiID: one Integer,
	taxiCapacity: one Integer,
	driverID: one Str,
	availability: one Bool,
	working: one Bool,
	requests: set Request,
	reservations: set Reservation
}
{
	(availability=True implies working=True) and (working=False implies availability=False)
}


sig Queue {
	ID: one Integer,
	drivers: set TaxiDriver
} 

sig System {
	reservations: set Reservation,
	requests: set Request,
	queues: set Queue,
	drivers: set TaxiDriver			
}

// *** FACTS ***

// only one System containing all the data
fact oneSystem {
	#System=1
	all r: Request | r in System.requests
	all q: Queue | q in System.queues
	all t: TaxiDriver | t in System.drivers
}

fact noDuplicateLocations {
	no disj l1, l2: Location | (l1.latitude=l2.latitude and l1.longitude=l2.longitude)
}

fact uniqueEmailAndPhones {
	no disj p1, p2: Passenger | (p1.email=p2.email)
	no disj p1, p2: Passenger | (p1.phone=p2.phone)
}

fact uniqueIDsRequest {
	no disj r1, r2: Request | (r1.ID=r2.ID)
}

fact uniqueIDsReservation {
	no disj r1, r2: Reservation | (r1.ID=r2.ID)
}


fact uniqueQueues {
	no disj q1, q2: Queue | (q1.ID=q2.ID)
}

fact uniqueTaxiDriver {
	no disj t1, t2: TaxiDriver | (t1.taxiID=t2.taxiID) and (t1.driverID=t2.driverID)
}


fact driverOnlyInOneQueue {
	all disj q1, q2: Queue | (q1.drivers & q2.drivers) = none
}

fact noRequestsFinishedBeforeBeingExecuted {
	all r: Request | (r.finishedAt.v > r.executedAt.v)
	all r: Reservation | (r.finishedAt.v > r.executedAt.v)
}

fact driverAvailableInOneQueue{
	all q: Queue | (all t: TaxiDriver | t in q.drivers iff t.availability=True)
}

fact noSameDriversTwoOverlappingRequests {
	all disj r1, r2: Request | (r1.driver & r2.driver)!=none 
			iff r2.finishedAt.v =< r1.executedAt.v or r2.executedAt.v >= r1.finishedAt.v
	all disj r1, r2: Reservation | (r1.driver & r2.driver)!=none 
			iff r2.finishedAt.v =< r1.executedAt.v or r2.executedAt.v >= r1.finishedAt.v
	all r1: Request, r2: Reservation | (r1.driver & r2.driver)!=none 
			iff r2.finishedAt.v =< r1.executedAt.v or r2.executedAt.v >= r1.finishedAt.v
}

fact driverRequestAndDriverReservationRelation {
	all d: TaxiDriver | (all r: Request | r in d.requests implies d in r.driver)
	all d: TaxiDriver | (all r: Reservation | r in d.reservations implies d in r.driver)
}

fact driversUnavailableDuringActiveRequestsOrReservations {
	all r: Request | (all d: TaxiDriver | r.active=True and d in r.driver implies (d.availability=False and d.working=True))
	all r: Reservation | (all d: TaxiDriver | r.active=True and d in r.driver implies (d.availability=False and d.working=True))
}

fact availableDriverMeansAlreadyFinishedAllHisRides {
	all d: TaxiDriver | (all r: Request | d.availability=True and r in d.requests implies r.active=False)
	all d: TaxiDriver | (all r: Reservation | d.availability=True and r in d.reservations implies r.active=False)
}

fact noSameDriverInDifferentActiveRequests {
	some disj r1, r2: Request | (r1.active=True and r2.active=True) implies ((r1.driver & r2.driver)=none)
	some disj r1, r2: Reservation | (r1.active=True and r2.active=True) implies ((r1.driver & r2.driver)=none)
	some r1: Request, r2: Reservation | (r1.active=True and r2.active=True) implies ((r1.driver & r2.driver)=none)
	
}

// *** ASSERTIONS ***

assert noReservationsTooSoon {
	no r: Reservation | (r.requestTime.v > minus[r.executedAt.v,2])
}

check noReservationsTooSoon

assert checkAddedRequest {
	all s, s': System, r: Request | addRequest[s, s', r] implies (r in s'.requests)
}

check checkAddedRequest

assert checkAddedReservation {
	all s, s': System, r: Reservation | addReservation[s, s', r, 1] implies (r in s'.reservations)
}

check checkAddedReservation

assert checkDriverAvailability {
	no r: Request | all d: TaxiDriver | (r.active=True and d.availability=True)
	no r: Reservation | all d: TaxiDriver | (r.active=True and d.availability=True)
}

check checkDriverAvailability

assert checkDriverNotWorking {
	no r: Request | (some d: TaxiDriver | d in r.driver and r.active=True and d.working=False)
	no r: Reservation | (some d: TaxiDriver | d in r.driver and r.active=True and d.working=False)
}

check checkDriverNotWorking

// *** PREDICATES ***

pred addRequest[s, s': System, r:Request] {
	s'.requests = s.requests + r
}

pred addReservation[s, s': System, r:Reservation, time: Int] {
	r.requestTime.v = time and
	s'.reservations = s.reservations + r
}

pred show {
	#Reservation>1
	#Request>1
	#{x: Reservation | x.active=False}>1
	#{x: Reservation | x.active=True}>1
	#{x: Request | x.active=True}>1
	#{x: Request | x.active=False}>1
}

// *** RUN COMMANDS ***

run addRequest
run addReservation
run show for 4
