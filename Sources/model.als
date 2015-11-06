open util/boolean
open util/integer 

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


sig Request {
	ID: one Integer,
	meetingPoint: one Location,
	people: one Int,
	passenger: one Passenger,
	active: one Bool,			// da mettere
	driver: some TaxiDriver,	// da cambiare
	executedAt: one SInt,		// da mettere
	finishedAt: one SInt		// da mettere
} 
{
	people>0
	#driver = div[people,3]
}


sig Reservation extends Request { // da cambiare
	requestTime: one SInt,
}
{
	requestTime.v<=minus[executedAt.v,2]
}

sig TaxiDriver {
	taxiID: one Integer,
	taxiCapacity: one Integer,
	driverID: one Str,
	availability: one Bool,
	working: one Bool,
	rides: set Request,
}
{
	(availability=True implies working=True) and (working=False implies availability=False)
}


sig Queue {
	ID: one Integer,
	drivers: set TaxiDriver
} 

sig System {
	requests: set Request,
	queues: set Queue,
	drivers: set TaxiDriver			
}

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
	no disj t1, t2: TaxiDriver | (t1.taxiID=t2.taxiID) or (t1.driverID=t2.driverID)
}


fact driverOnlyInOneQueue {
	all d: TaxiDriver | (d in Queue.drivers and all q1, q2: Queue | (d in q1.drivers and d in q2.drivers) implies q1=q2)
}

fact noRequestsFinishedBeforeBeingExecuted {
	all r: Request | (r.finishedAt.v > r.executedAt.v)
}


fact driverAvailableInOneQueue{
	all q : Queue | TaxiDriver in q.drivers implies TaxiDriver.availability=True
	
}

fact noSameDriversTwoOverlappingRequests {
	all disj r1, r2: Request | (r1.driver & r2.driver)!=none 
			iff r2.finishedAt.v =< r1.executedAt.v or r2.executedAt.v >= r1.finishedAt.v
}

fact {
	all d: TaxiDriver | (some r: Request | r in d.rides iff d in r.driver)
}

fact {
	all r: Request | (r.active=True iff all d: TaxiDriver | d in r.driver and d.availability=False)
	
}

assert noReservationsTooSoon {
	no r: Reservation |  (r.requestTime.v > r.executedAt.v - 2)
}

check noReservationsTooSoon

assert checkAddedRequest{
	all s, s': System, r: Request | addRequest[s, s', r] implies (r in s'.requests)
}

check checkAddedRequest

assert checkAddedReservation{
	all s, s': System, r: Reservation | addReservation[s, s', r, 1] implies (r in s'.requests)
}

check checkAddedReservation

pred addRequest[s, s': System, r:Request]{
	s'.requests = s.requests + r
}

pred addReservation[s, s': System, r:Reservation, time: Int]{
	r.requestTime.v = time and
	s'.requests = s.requests + r
}

pred show {
	#{x: Request | x.active=True}>1
}

run addRequest
run addReservation
run show for 5
