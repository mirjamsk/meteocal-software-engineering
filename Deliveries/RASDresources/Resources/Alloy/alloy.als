sig User {
	calendar: one Calendar, 
	notifications: set Notification
}

sig Calendar {
	events: set Event
}

abstract sig Event {
	organizer: one User, 
	participants: some User, 
	location: one Location,
	weatherForecast: one WeatherForecast
}

sig OutdoorEvent extends Event {}

sig IndoorEvent extends Event {}

sig Location{}

sig WeatherForecast {
	weatherInformation: one Weather
}

sig Weather { }

abstract sig Notification {
		linkedTo: one Event	
}
sig WeatherNotification extends Notification{}
sig InvitationNotification extends Notification{}

//facts
fact everyCalendarHasOneUser{
	all c: Calendar | one u:User | c = u.calendar
}
fact everyUserHasAUniqueCalendar{
	no disj u1, u2: User | u1.calendar = u2.calendar
}

fact everyCalendarContainsOnlyParticipatingEvents{
	all u: User, e: Event | (e in u.calendar.events) <=> ( u in e.participants)
}

fact eveyEventHasAOneOrganizer{
	all e:Event | one u:User | u = e.organizer
}

fact organizerIsAlsoParticipant{
	all  e: Event | e.organizer in e.participants
}

fact eachLocationIsLinkedToAnEvent{
	all l: Location | some e: Event | l = e.location
}

fact eachWeatherForecastIsLinkedToAnEvent{
	all wf: WeatherForecast | one e: Event | wf = e.weatherForecast
}

fact eachWeatherIsAsociatedWithOneWF{
	all w: Weather | one wf: WeatherForecast | w = wf.weatherInformation
}

fact allNofiticationsAreMeantForAUser{
 	all i: Notification | one u: User | i in u.notifications
}


fact organizerCannotGetInvitationForOwnEvent{
	all e: Event,  i:InvitationNotification |( e= i.linkedTo) =>( i not in e.organizer.notifications )
}

fact participantCannotGetReinvitated{
	all e: Event,  i:InvitationNotification |( e= i.linkedTo) =>( i not in e.participants.notifications )
}


//a. User cannot get 2 invitations to the same event
//b. User cannot get 2 weatherNotifications about the same event 
//c. User cannot get weathern ofits about event he has a pending invitation (not a participant)
fact onlyOneNotifAboutAsingleEventPerUser{
	all u: User, disj n1, n2: WeatherNotification | 
		(n1.linkedTo = n2.linkedTo) =>((n1+n2)  not  in u.notifications)
}

fact allWeatherNofiticationsAreMeantForAParticipant{
 	all i: WeatherNotification | one u: User | (i in u.notifications)<=> (u in i.linkedTo.participants)
}
//PREDICATES
pred show() {}


run show for 3
