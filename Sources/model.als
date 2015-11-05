sig Integer {}
sig Real {
	integer_part: one Int,
  	fractional_part: one Int
}
sig Str {}
sig Location {
	latitude: one Real,
	longitude: one Real
}

sig PhoneNumber {
	number: one Int
}

enum DriverStatus {Available, Unavailable}
enum RideStatus {Scheduled, Processed, Ended}

abstract sig User {}
abstract sig DateTime {
	day: one Int,
 	month: one Int,
	year: one Int,
	hour: one Int,
	minute: one Int
}

sig Visitor extends User {}
sig RegisteredPassenger extends User {
	name: one Str,
	surname: one Str,
	email: one Str,
	phoneNumber: one PhoneNumber,
 	password: one Str
}

sig Driver extends User {
	ID: one Integer,
	password: one Str,
	status: one DriverStatus
}

sig Taxi {
	ID: one Integer,
	capacity: one Integer,
	driver: one Driver
}

sig Request {
	meetingPoint: one Location,
	people: one Int,
	status: one RideStatus,
	passenger: one RegisteredPassenger,
	taxi: one Taxi
}

sig Reservation extends Request {
	dateTime: one DateTime
}

sig Queue {
	taxis: set Taxi
}

fact noDuplicateInts {
	all disj i, j: Int | int i != int j
}

fact noInvalidDateTime {
	all dt: DateTime | (#dt.day=1) and (#dt.month=1) and (#dt.year=1) and (#dt.hour=1) and (#dt.minute=1)
	no dt: DateTime | (int dt.day < 0) and (int dt.month < 0) and (int dt.year < 0)	
	no dt: DateTime | (int dt.day > 31) and (int dt.month > 12)
}

fact oneTaxiPerDriver {
	all t: Taxi | (one d: Driver | t.driver=d)
}

fact oneTaxiPerRequest {
	all r: Request | (one t: Taxi | r.taxi = t)
}

fact oneRegisteredPassengerPerRequest {
	all r: Request | (one rp: RegisteredPassenger | r.passenger = rp) 
}

fact noRepeatedLocations {
	no disj l1, l2: Location | (l1.latitude = l2.latitude and l1.longitude = l2.longitude)
}

fact noDuplicateUsers {
	no disj p1, p2: RegisteredPassenger | (p1.email=p2.email) or (p1.phoneNumber=p2.phoneNumber)
}

fact noDuplicateTaxis {
	no disj t1, t2: Taxi | (t1.ID=t2.ID)
}

fact noDuplicateDrivers {
	no disj d1, d2: Driver | (d1.ID=d2.ID)
}

fact taxiInQueueIsAvailable {
	all t: Taxi | (one q: Queue | t in q.taxis and t.driver.status=Available)
}

fact taxiNotInQueueIsUnavailable {
	all t: Taxi | (no q: Queue | t in q.taxis and t.driver.status=Unavailable)
}

fact {
	all r: Request, q: Queue | (one t: Taxi | r.taxi = t and t.driver.status=Unavailable and t not in q.taxis)
}

assert noRequestsWithoutPassenger {
	no r: Request | (no rp: RegisteredPassenger | r.passenger = rp)	
}

check noRequestsWithoutPassenger for 5

assert oneTaxiBusyOnRequestProcessing {
	no r: Request | (r.status=Processed implies all t: Taxi | t.driver.status=Available)
}

check oneTaxiBusyOnRequestProcessing for 5
